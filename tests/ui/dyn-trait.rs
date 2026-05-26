use std::fmt::Display;

// Opaque because we don't support unsize coercions.
fn construct<T: Display + 'static>(x: T) -> Box<dyn Display> {
    Box::new(x)
}

fn destruct(x: &dyn Display) -> String {
    x.to_string()
}

// Opaque because we don't support unsize coercions.
fn combine() {
    let x = String::new();
    let _ = destruct(&*construct(x));
}

fn foo<T>(_: &(dyn (for<'a> Fn(&'a T) -> T) + 'static), _: &dyn PartialEq<Option<T>>) {}

fn bar(_: &dyn (Fn(&dyn Display))) {}
