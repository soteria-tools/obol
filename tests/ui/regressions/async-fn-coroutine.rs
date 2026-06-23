//@ output=pretty-llbc
//! Limitation regression test: `async fn` lowers to a coroutine, which obol does
//! not support. The item must be dropped *gracefully* (a `caused errors; ignoring`
//! diagnostic and a non-zero error count) rather than crashing the whole tool.
//! If obol gains coroutine support this output will change and the test should be
//! updated to reflect the real translation.
pub async fn increment(x: u32) -> u32 {
    x + 1
}

pub fn use_async_block() -> impl std::future::Future<Output = u32> {
    async { 1u32 + 2 }
}
