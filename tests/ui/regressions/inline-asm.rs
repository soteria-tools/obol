//@ output=pretty-llbc
//! Limitation regression test: inline `asm!` is not supported. The function is
//! still translated, but its body is replaced by an `error("Inline assembly is
//! not supported")` node rather than crashing. Documents that obol degrades
//! gracefully on inline assembly.
use std::arch::asm;

pub unsafe fn add_via_asm(mut x: u64) -> u64 {
    asm!("add {0}, {0}", inout(reg) x);
    x
}
