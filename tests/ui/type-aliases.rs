//! Type aliases in various positions. Plain `type X = Y` aliases are normalized away by rustc, so
//! these mostly check that we follow the alias to the underlying type. The interesting case is the
//! associated-type projection in the `impl Sink<...>` name: it reaches us as an unresolved alias
//! type that we normalize to the concrete `u8` rather than emitting an error placeholder.

// Plain alias to a concrete type.
pub type Length = usize;

// Generic alias, and an alias of an alias.
pub type Pair<T> = (T, T);
pub type Bytes = Pair<u8>;

// Alias used in a const-generic (array length) position.
pub type Buffer = [Length; 4];

pub struct Holder<T>(pub T);

pub trait Carrier {
    type Item;
}
impl Carrier for u32 {
    type Item = u8;
}

// The trait-ref argument `<u32 as Carrier>::Item` is an associated-type projection over a concrete
// type. It is kept in the impl's name as an alias; we normalize it to `u8`.
pub trait Sink<X> {
    fn sink(self);
}
impl Sink<<u32 as Carrier>::Item> for Holder<u32> {
    fn sink(self) {}
}

// Polymorphic counterpart: `Sink<T::Item>` is implemented for every `T: Carrier`, so the impl block
// itself stays polymorphic and its name carries the *unresolved* projection `<T as Carrier>::Item`.
// With `T` still free there is nothing to normalize, so the alias can't be resolved. The concrete
// method `sink::<u32>` is still translated correctly — only the polymorphic impl's display name
// degrades to an error placeholder. This is the boundary of what a monomorphic-focused tool can do.
pub struct PolyWrap<T>(pub T);
impl<T: Carrier> Sink<T::Item> for PolyWrap<T> {
    fn sink(self) {}
}

// A function polymorphic on `T` whose argument is an alias (`T::Item`) over that type parameter.
// Each call site monomorphizes it, so the alias resolves per-instantiation.
pub fn feed<T: Carrier>(_x: T::Item) {}

pub fn main() {
    let _len: Length = 3;
    let _bytes: Bytes = (1, 2);
    let _buf: Buffer = [0; 4];
    Holder(5u32).sink();
    PolyWrap(9u32).sink();
    feed::<u32>(7u8);
}
