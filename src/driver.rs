//! This module provides a compiler driver such that:
//!
//! 1.  the rustc compiler context is available
//! 2.  the rustc `stable_mir` APIs are available
//!
//! It exports a single function:
//!
//! ```rust,ignore
//! stable_mir_driver(args: &Vec<String>, callback_fn: fn (TyCtxt) -> () )
//! ```
//!
//! Calling this function is essentially equivalent to the following macro call:
//!
//! ```rust,ignore
//! rustc_internal::run_with_tcx!( args, callback_fn );
//! ```
//!
//! However, we prefer a non-macro version for clarity and build simplicity.

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_smir;
extern crate stable_mir;
use rustc_driver::Compilation;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::TyCtxt;
use stable_mir::rustc_internal;

use crate::args::CliOpts;

struct StableMirCallbacks {
    callback_fn: fn(&CliOpts, TyCtxt) -> (),
    cli_opts: CliOpts,
}

impl rustc_driver::Callbacks for StableMirCallbacks {
    fn after_analysis(&mut self, _compiler: &Compiler, tcx: TyCtxt) -> Compilation {
        let _ = rustc_internal::run(tcx, || (self.callback_fn)(&self.cli_opts, tcx));

        Compilation::Stop
    }
}

pub fn stable_mir_driver(mut cli_opts: CliOpts, callback_fn: fn(&CliOpts, TyCtxt) -> ()) {
    let rustc = std::mem::take(&mut cli_opts.rustc);
    let mut callbacks = StableMirCallbacks {
        callback_fn,
        cli_opts,
    };
    let early_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());
    rustc_driver::init_rustc_env_logger(&early_dcx);
    let _ = rustc_driver::run_compiler(&rustc, &mut callbacks);
}
