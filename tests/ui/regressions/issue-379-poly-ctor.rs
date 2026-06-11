//@ output=pretty-llbc
//! Regression test for https://github.com/soteria-tools/soteria/issues/379
//! Passing an enum variant as a function value (e.g. `opt.map(Some)`) reaches the
//! variant's constructor instance, whose body `Instance::body()` doesn't provide.
//! Obol used to fall back to the *generic* constructor MIR and translate it without
//! substituting the instance's arguments, leaking free type parameters and emitting
//! spurious "translate_ty got a type parameter" / "Failed to compute layout for
//! `Option<T>`" errors even though all translated code is monomorphic. We now
//! instantiate the fallback body with the instance's args, so the constructors come
//! out fully monomorphic.
pub fn wrap_some(x: Option<u32>) -> Option<Option<u32>> {
    x.map(Some)
}

pub fn wrap_ok(x: Option<u32>) -> Option<Result<u32, u8>> {
    x.map(Ok)
}
