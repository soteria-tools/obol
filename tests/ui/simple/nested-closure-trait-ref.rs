fn foo<T: Clone>(x: T) -> impl Fn() -> T {
    let f = move || move || x.clone();
    f()
}

fn main() {
    let x = 42;
    let f = foo(x);
    assert_eq!(f(), 42);
}
