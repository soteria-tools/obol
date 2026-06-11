//@ output=pretty-llbc
//! Regression test for https://github.com/soteria-tools/soteria/issues/379
//! A `&dyn Trait` constant used to panic with "Translating unsized dyn constant?"
//! because the pointee was registered as a global with the unsized `dyn Trait`
//! type, which has no layout. We now recover the concrete (sized) type from the
//! vtable provenance and translate the pointee with that type, building the
//! `&dyn Trait` as a reference with the right unsizing metadata.
pub trait MyTrait {
    fn val(&self) -> u32;
}

struct S;
impl MyTrait for S {
    fn val(&self) -> u32 {
        42
    }
}

const C: &dyn MyTrait = &S;

pub fn get() -> &'static dyn MyTrait {
    C
}
