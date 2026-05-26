fn foo<T>() -> usize {
    const { 42 }
}

fn main() {
    let _ = foo::<u8>();
}
