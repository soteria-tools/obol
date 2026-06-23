//@ output=pretty-llbc
//! Limitation regression test: an explicit `#[coroutine]` closure produces a
//! coroutine type, which obol does not support. The item must be dropped
//! gracefully with a `Coroutine types are not supported yet` error rather than
//! panicking.
#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::Coroutine;

pub fn make() -> impl Coroutine<Yield = i32, Return = ()> {
    #[coroutine]
    || {
        yield 1;
        yield 2;
    }
}
