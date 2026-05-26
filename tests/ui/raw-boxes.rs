unsafe fn foo() {
    let b = Box::new(42);
    let p = Box::into_raw(b);
    let _ = Box::leak(Box::new(42));
    let b = Box::from_raw(p);
    let i = *b;
}
