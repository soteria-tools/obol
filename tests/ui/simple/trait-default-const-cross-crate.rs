//@aux-crate=trait-default-const.rs
//@obol-args=--extract-opaque-bodies
fn bar<T>() {
    trait_default_const::foo::<T>();
}
