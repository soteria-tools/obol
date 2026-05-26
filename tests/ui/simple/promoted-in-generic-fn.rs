fn f<T>() {
    // This can't be evaluated generically.
    let _ = &size_of::<T>();
}

fn main() {
    f::<u8>();
}
