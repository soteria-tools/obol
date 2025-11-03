#![feature(rustc_private)]
#![feature(iterator_try_collect)]
#![feature(iter_array_chunks)]

pub mod args;

/// The version of the crate, as defined in `Cargo.toml`.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
