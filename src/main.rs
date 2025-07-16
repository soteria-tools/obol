#![feature(rustc_private)]
#![feature(iterator_try_collect)]
#![feature(iter_array_chunks)]

pub mod args;
pub mod driver;
pub mod printer;
pub mod translate;
use clap::Parser;
use driver::stable_mir_driver;
use printer::emit_smir;

fn main() {
    let cli = args::CliOpts::parse();
    stable_mir_driver(cli, emit_smir);
}
