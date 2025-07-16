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
    /// Args that `rustc` accepts.
    #[arg(last = true)]
    pub rustc: Vec<String>,
}
