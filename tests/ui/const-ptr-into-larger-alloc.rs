//! A `*const u8` constant pointing into a larger, over-aligned allocation (as in
//! hashbrown's `Group::static_empty`). Two things are checked:
//!
//! - The pointed-to anonymous global keeps the whole allocation's size and
//!   alignment, rather than being truncated to the `u8` pointee type: the global
//!   is recorded as `[u64; 1]` (8 bytes, aligned to 8) when reached only through a
//!   `*const u8`, not as a single `u8`.
//! - `ALIGNED` and `PTR` point into the *same* allocation, so they translate to a
//!   *single* global and compare equal (the allocation is one object, regardless
//!   of the pointee type each pointer views it through). When the allocation is
//!   also reached through `&Aligned`, that fully-typed view is the one recorded.

#[repr(C, align(8))]
pub struct Aligned([u8; 8]);

pub const ALIGNED: &Aligned = &Aligned([0; 8]);
pub const PTR: *const u8 = ALIGNED.0.as_ptr();

pub fn main() {
    assert!(ALIGNED as *const Aligned as *const u8 == PTR);
}
