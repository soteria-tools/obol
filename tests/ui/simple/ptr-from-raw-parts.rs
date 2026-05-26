#![feature(ptr_metadata)]

fn main() {
    let a = [1u32; 2];
    let _: *const [u32] = core::ptr::from_raw_parts(&raw const a, 2);
}
