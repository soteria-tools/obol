//@ output=pretty-llbc
//! Regression test for https://github.com/soteria-tools/soteria/issues/379
//! A constant holding a function address as a raw pointer (`f as *const ()`)
//! used to panic with "Shouldn't reach a global function": the pointer's
//! provenance is a function, and we tried to register that function as a global.
//! This pattern shows up in ifunc-style runtime dispatch caches (e.g. `memchr`'s
//! `detect`, `yansi`'s `Condition`). We now translate it as a function pointer.
fn target() -> bool {
    true
}

struct Holder(*const ());

const C: Holder = Holder(target as *const ());

pub fn get() -> *const () {
    C.0
}
