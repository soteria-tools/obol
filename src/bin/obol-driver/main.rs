#![feature(rustc_private)]
#![feature(iterator_try_collect)]
#![feature(iter_array_chunks)]
#![feature(impl_trait_in_bindings)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_public;
extern crate rustc_session;

pub mod driver;
pub mod transform;
pub mod translate;

use std::{env, fmt, panic, path::PathBuf};

use charon_lib::{
    export::CrateData, logger, options::SerializationFormat, transform::TransformCtx,
};
use obol_lib::args::{self, OutputFormat};

pub enum ObolError {
    /// Number of errors encountered during translation.
    ObolError(usize),
    RustcError,
    Panic,
    Serialize,
}

impl fmt::Display for ObolError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ObolError::RustcError => write!(f, "Code failed to compile")?,
            ObolError::ObolError(err_count) => {
                write!(f, "Obol failed to translate this code ({err_count} errors)")?
            }
            ObolError::Panic => write!(f, "Compilation panicked")?,
            ObolError::Serialize => write!(f, "Could not serialize output file")?,
        }
        Ok(())
    }
}

fn run_passes(ctx: &mut TransformCtx) {
    use charon_lib::transform::*;
    // Passes that apply to the whole crate at once, typically those that change item signatures.
    let global = |x| Pass::NonBody(CowBox::Borrowed(x));
    // Passes that apply to bodies but work on either kind.
    let mixed_body = |x| Pass::NonBody(CowBox::Borrowed(x));

    // Item and type cleanup passes.
    ctx.run_pass(
        // Compute short names. We do it early to make pretty-printed output more legible in traces.
        global(&add_missing_info::compute_short_names::Transform),
    );

    // Body cleanup passes on the ullbc.
    let pass = Pass::FusedUnstructuredBody(Box::new([
        // Compute the metadata & insert for Rvalue
        CowBox::Borrowed(&finish_translation::insert_ptr_metadata::Transform),
        // Add the missing assignments to the return value.
        // When the function return type is unit, the generated MIR doesn't set the return value to
        // `()`. This can be a concern: in the case of Aeneas, it means the return variable
        // contains ⊥ upon returning. For this reason, when the function has return type unit, we
        // insert an extra assignment just before returning.
        CowBox::Borrowed(&finish_translation::insert_assign_return_unit::Transform),
        // Insert `StorageLive` for locals that don't have one (that's allowed in MIR).
        CowBox::Borrowed(&finish_translation::insert_storage_lives::Transform),
        // Inline all asserts that correspond to dynamic checks into statements.
        // The following pass will then merge the generated gotos as part of this substitution,
        // and [reconstruct_fallible_operations] can then use the inlined asserts to
        // reconstruct the fallible operations.
        CowBox::Borrowed(&resugar::move_asserts_to_statements::Transform),
        // Merge single-origin gotos into their parent. This drastically reduces the graph size
        // of the CFG.
        // This must be done early as some resugaring passes depend on it.
        CowBox::Borrowed(&control_flow::merge_goto_chains::Transform),
        // Remove overflow/div-by-zero/bounds checks since they are already part of the
        // arithmetic/array operation in the semantics of (U)LLBC.
        // **WARNING**: this pass uses the fact that the dynamic checks introduced by Rustc use a
        // special "assert" construct. Because of this, it must happen *before* the
        // [reconstruct_asserts] pass. See the comments in [crate::remove_dynamic_checks].
        // **WARNING**: this pass relies on a precise structure of the MIR statements. Because of this,
        // it must happen before passes that insert statements like [simplify_constants].
        CowBox::Borrowed(&resugar::reconstruct_fallible_operations::Transform),
        // Reconstruct the asserts
        CowBox::Borrowed(&resugar::reconstruct_asserts::Transform),
        // Replace TypeId construction constants with ConstantExprKind::TypeId(T) before
        // simplify_constants desugars them into statement sequences.
        transform::uneval_typeid::Transform::new(ctx),
        // Reconstruct pointer null-checks to avoid reasoning about pointer-to-integer transmutations.
        CowBox::Borrowed(&transform::reconstruct_ptr_null_checks::Transform),
        // Desugar the constants to other values/operands as much as possible.
        CowBox::Borrowed(&simplify_output::simplify_constants::Transform),
        // Remove locals of type `()` which show up a lot.
        CowBox::Borrowed(&simplify_output::remove_unit_locals::Transform),
        // Another round.
        CowBox::Borrowed(&control_flow::merge_goto_chains::Transform),
        // Filter the "dangling" blocks. Those might have been introduced by, for instance,
        // [`merge_goto_chains`].
        CowBox::Borrowed(&normalize::filter_unreachable_blocks::Transform),
        // Make sure the block ids used in the ULLBC are consecutive
        CowBox::Borrowed(&simplify_output::update_block_indices::Transform),
    ]));
    ctx.run_pass(pass);

    // Cleanup passes useful for both llbc and ullbc.
    ctx.run_passes([
        // Remove the locals which are never used.
        mixed_body(&simplify_output::remove_unused_locals::Transform),
        // Remove the useless `StatementKind::Nop`s.
        mixed_body(&simplify_output::remove_nops::Transform),
        // Reorder the graph of dependencies and compute the strictly connex components to:
        // - compute the order in which to extract the definitions
        // - find the recursive definitions
        // - group the mutually recursive definitions
        // This is done last to account for the final item graph, not the initial one.
        global(&add_missing_info::reorder_decls::Transform),
    ]);
}

/// Run obol. Returns the number of warnings generated.
fn run_obol(options: args::CliOpts) -> Result<usize, ObolError> {
    // Run the driver machinery.
    let Some(mut ctx) = driver::run_rustc_driver(&options)? else {
        // We didn't run charon.
        return Ok(0);
    };

    // The bulk of the translation is done, we no longer need to interact with rustc internals. We
    // run several passes that simplify the items and cleanup the bodies.
    run_passes(&mut ctx);

    let error_count = ctx.errors.borrow().error_count;

    if options.print_ullbc {
        println!("\n// Final ULLBC:\n\n{ctx}\n");
    }

    if !options.no_serialize {
        let crate_data = CrateData::new(ctx);

        let serial_fmt = match options.format {
            OutputFormat::Json => SerializationFormat::Json,
            OutputFormat::Postcard => SerializationFormat::Postcard,
        };

        let path = options.dest_file.clone().unwrap_or_else(|| {
            let crate_name = &crate_data.translated.crate_name;
            let extension = match serial_fmt {
                SerializationFormat::Json => "ullbc",
                SerializationFormat::Postcard => "ullbc.postcard",
            };
            PathBuf::from(format!("{crate_name}.{extension}"))
        });

        crate_data
            .serialize_to_file(&path, serial_fmt)
            .expect("Failed to write output");
    }

    Ok(error_count)
}

fn main() {
    // Initialize the logger
    logger::initialize_logger();

    // Retrieve the Charon options by deserializing them from the environment variable
    // (cargo-charon serialized the arguments and stored them in a specific environment
    // variable before calling cargo with RUSTC_WRAPPER=charon-driver).
    let options: args::CliOpts = match env::var(args::OBOL_ARGS) {
        Ok(opts) => serde_json::from_str(opts.as_str()).unwrap(),
        Err(_) => Default::default(),
    };

    // Catch any and all panics coming from charon to display a clear error.
    let res = panic::catch_unwind(move || run_obol(options))
        .map_err(|_| ObolError::Panic)
        .flatten();

    match res {
        Ok(warn_count) => {
            if warn_count != 0 {
                let msg = format!("The extraction generated {} warnings", warn_count);
                eprintln!("warning: {}", msg);
            }
        }
        Err(err) => {
            log::error!("{err}");
            let exit_code = match err {
                ObolError::ObolError(_) | ObolError::Serialize => 1,
                ObolError::RustcError => 2,
                // This is a real panic, exit with the standard rust panic error code.
                ObolError::Panic => 101,
            };
            std::process::exit(exit_code);
        }
    }
}
