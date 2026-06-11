//! Exercises the `reconstruct_ptr_null_checks` pass: a pointer null-check should be
//! reconstructed into a call to the `@ZeroIfNull` builtin rather than a raw
//! `transmute::<*T, usize>` feeding a `switch [0, _]`.

#[no_mangle]
pub fn is_null_const(p: *const u8) -> bool {
    p.is_null()
}

#[no_mangle]
pub fn is_null_mut(p: *mut i32) -> bool {
    p.is_null()
}

#[no_mangle]
pub fn branch_on_null(p: *const u32) -> u32 {
    if p.is_null() { 0 } else { unsafe { *p } }
}
