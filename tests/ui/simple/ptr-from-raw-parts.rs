//@ obol-args=--exclude=core::ptr::metadata::Thin
//@ obol-args=--exclude=core::ptr::metadata::Pointee
//@ obol-args=--include=core::ptr::metadata::from_raw_parts
#![feature(ptr_metadata)]

fn main() {
    let a = [1u32; 2];
    let _: *const [u32] = core::ptr::from_raw_parts(&raw const a, 2);
}
