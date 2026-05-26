trait Trait {
    type Type;
}

impl Trait for u32 {
    type Type = bool;
}

struct Foo<T: Trait>(T::Type);

fn foo(_x: Foo<u32>) {}
