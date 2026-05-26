fn main() {
    let s = [11, 42];
    let ptr = s.as_ptr();
    unsafe {
        assert!(*ptr.offset(1) == 42);
    }
}
