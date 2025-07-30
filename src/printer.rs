extern crate rustc_middle;
extern crate rustc_monomorphize;
extern crate rustc_session;
extern crate rustc_smir;
extern crate rustc_span;
extern crate stable_mir;
// HACK: typically, we would source serde/serde_json separately from the compiler
//       However, due to issues matching crate versions when we have our own serde
//       in addition to the rustc serde, we force ourselves to use rustc serde
extern crate serde;
extern crate serde_json;
use charon_lib::{export::CrateData, transform::Pass};
use rustc_middle::ty::TyCtxt;
use rustc_session::config::{OutFileName, OutputType};

use crate::translate::translate_crate::translate;

// Serialization Entrypoint
// ========================

pub fn emit_smir(opts: &crate::args::CliOpts, tcx: TyCtxt<'_>) {
    let mut ctx = translate(&opts, tcx);
    use Pass::*;
    use charon_lib::transform::*;
    let transforms: &[Pass] = &[
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
    ];
    for pass in transforms {
        pass.run(&mut ctx);
    }

    if opts.print_ullbc {
        println!("\n// Final ULLBC:\n\n{ctx}\n");
    }

    let path = opts.dest_file.clone().or_else(|| {
        if let OutFileName::Real(path) = tcx.output_filenames(()).path(OutputType::Mir) {
            Some(path.with_extension("ullbc"))
        } else {
            None
        }
    });

    if let Some(path) = path {
        let crate_data = CrateData::new(ctx);
        crate_data
            .serialize_to_file(&path)
            .expect("Failed to write smir.json to output")
    }
}
