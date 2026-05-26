//@ obol-args=--opaque core::alloc::layout::_::new
//@ obol-args=--opaque core::alloc::layout::_::from_size_align_unchecked
//@ obol-args=--opaque core::alloc::layout::Layout

use std::mem;
use std::ptr;

fn write<T>(x: &mut T, y: &T) {
    unsafe {
        ptr::copy_nonoverlapping(y, x, 1);
    }
}
