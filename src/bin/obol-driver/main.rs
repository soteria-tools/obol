#![feature(rustc_private)]
#![feature(iterator_try_collect)]
#![feature(iter_array_chunks)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_smir;
extern crate stable_mir;

pub mod driver;
pub mod translate;

use std::{env, fmt, panic, path::PathBuf};

use charon_lib::{export::CrateData, logger, transform::Pass};
use obol_lib::args::{self, CliOpts};

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

fn transformation_passes(_opts: &CliOpts) -> Vec<Pass> {
    use Pass::*;
    use charon_lib::transform::*;
    vec![
        NonBody(&compute_short_names::Transform),
        UnstructuredBody(&merge_goto_chains::Transform),
        UnstructuredBody(&remove_dynamic_checks::Transform),
        UnstructuredBody(&simplify_constants::Transform),
        UnstructuredBody(&reconstruct_asserts::Transform),
        UnstructuredBody(&filter_unreachable_blocks::Transform),
        UnstructuredBody(&inline_local_panic_functions::Transform),
        UnstructuredBody(&insert_assign_return_unit::Transform),
        UnstructuredBody(&remove_unit_locals::Transform),
        UnstructuredBody(&remove_drop_never::Transform),
        NonBody(&remove_unused_locals::Transform),
        NonBody(&insert_storage_lives::Transform),
        NonBody(&remove_nops::Transform),
        NonBody(&reorder_decls::Transform),
    ]
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
    for pass in transformation_passes(&options) {
        pass.run(&mut ctx);
    }

    let error_count = ctx.errors.borrow().error_count;

    if options.print_ullbc {
        println!("\n// Final ULLBC:\n\n{ctx}\n");
    }

    let crate_data = CrateData::new(ctx);

    let path = options.dest_file.clone().or_else(|| {
        let crate_name = &crate_data.translated.crate_name;
        let extension = "ullbc";
        Some(PathBuf::from(format!("{crate_name}.{extension}")))
    });

    if let Some(path) = path {
        crate_data
            .serialize_to_file(&path)
            .expect("Failed to write smir.json to output")
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
