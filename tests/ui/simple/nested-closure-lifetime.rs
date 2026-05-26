fn foo<'a, T: Clone>(x: &'a T) -> impl Fn() -> &'a T {
    let f = move || move || x;
    f()
}

fn main() {
    let x = 42;
    let f = foo(&x);
    assert_eq!(f(), &42);
}
