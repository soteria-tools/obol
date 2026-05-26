pub struct Foo<F>(F);

impl<F> Foo<F> {
    pub fn method<T>() {
        let _promoted = &0;
    }
}

fn main() {
    Foo::<fn()>::method::<u32>();
}
