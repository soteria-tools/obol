use std::path::PathBuf;

use serde::Deserialize;
use serde_derive::Serialize;

pub const OBOL_ARGS: &str = "OBOL_ARGS";

#[derive(Debug, Default, Clone, clap::Parser, Serialize, Deserialize)]
#[clap(name = "Obol")]
pub struct CliOpts {
    #[clap(
        long = "cargo",
        help = "If Obol should compile the crate using Cargo; otherwise, uses rustc to compile a single file."
    )]
    pub use_cargo: bool,
    /// The destination file. By default `<dest_dir>/<crate_name>.ullbc`.
    #[clap(long = "dest-file", value_parser)]
    pub dest_file: Option<PathBuf>,
    #[clap(
        long = "print-ullbc",
        help = "Print the ULLBC after applying the micro-passes."
    )]
    pub print_ullbc: bool,
    #[clap(
        long = "entry-names",
        help = "List of function names that count as entry points to generate; if none are specified, main is used."
    )]
    pub entry_names: Vec<String>,
    #[clap(
        long = "entry-attribs",
        help = "List of attributes (e.g. `kani::proof`) that count as entry points to generate; empty by default."
    )]
    pub entry_attribs: Vec<String>,
    /// Args that are passed to the underlying tool (`rustc` or `cargo` depending on `--cargo`).
    #[arg(last = true)]
    pub spread: Vec<String>,
}
