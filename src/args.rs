use std::path::PathBuf;

#[derive(Debug, Default, Clone, clap::Parser)]
#[clap(name = "Obol")]
pub struct CliOpts {
    /// The destination file. By default `<dest_dir>/<crate_name>.ullbc`.
    #[clap(long = "dest-file", value_parser)]
    pub dest_file: Option<PathBuf>,
    #[clap(
        long = "print-ullbc",
        help = "Print the ULLBC after applying the micro-passes."
    )]
    pub print_ullbc: bool,
    #[clap(
        long = "entry_names",
        help = "List of function names that count as entry points to generate; if none are specified, main is used."
    )]
    pub entry_names: Vec<String>,
    #[clap(
        long = "entry_attribs",
        help = "List of attributes (e.g. `kani::proof`) that count as entry points to generate; empty by default."
    )]
    pub entry_attribs: Vec<String>,
    /// Args that `rustc` accepts.
    #[arg(last = true)]
    pub rustc: Vec<String>,
}
