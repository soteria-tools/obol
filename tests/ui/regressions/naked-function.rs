//@ output=pretty-llbc
//! Limitation regression test: a `#[naked]` function is implemented purely with
//! `naked_asm!`, which obol cannot translate (inline assembly). Documents that
//! the body degrades to an `error("Inline assembly is not supported")` node
//! rather than panicking.
#![feature(naked_functions)]

use std::arch::naked_asm;

#[unsafe(naked)]
pub extern "C" fn just_return() {
    naked_asm!("ret");
}
