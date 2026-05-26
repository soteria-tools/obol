//@ known-failure
pub trait Foo {
    type Size: Copy;
}

pub trait Bar {
    type Item<T>: Foo;
}
