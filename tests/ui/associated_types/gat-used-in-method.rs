trait Foo {
    type T<A>;
    fn f<A>(x: Self::T<A>);
}
