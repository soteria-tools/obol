//@ output=pretty-llbc
//! Limitation regression test: an `async` closure (`async || ...`) is a
//! `CoroutineClosure`, whose stable-MIR conversion currently hits a `todo!()`
//! inside `rustc_public` (`convert/stable/ty.rs`). obol's per-item
//! `catch_unwind` must turn this into a `Thread panicked when extracting item`
//! diagnostic and drop the item, instead of bringing the whole tool down.
#![feature(async_closure)]

pub fn make() -> impl AsyncFn(u32) -> u32 {
    async |x: u32| x + 1
}
