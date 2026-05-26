//@ rustc-args=-C opt-level=3
#![feature(core_intrinsics)]
#![allow(internal_features)]

fn discriminant_value<T>(opt: &Option<T>) -> isize {
    core::intrinsics::discriminant_value(opt)
}

fn is_some<T>(opt: Option<T>) -> bool {
    discriminant_value(&opt) != 0
}

// This doesn't optimize to a bare discriminant read :(
fn my_is_some<T>(opt: Option<T>) -> isize {
    match opt {
        Some(_) => 1,
        None => 0,
    }
}

fn main() {
    let x: Option<u32> = Some(42);
    assert!(is_some(x));
    assert_eq!(my_is_some(x), 1);

    let y: Option<u32> = None;
    assert!(!is_some(y));
    assert_eq!(my_is_some(y), 0);
}
