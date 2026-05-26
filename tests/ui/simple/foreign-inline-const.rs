//@ aux-crate=closure-inside-inline-const.rs
//@ obol-args=--include=closure_inside_inline_const
fn bar<T>() {
    closure_inside_inline_const::foo::<T>();
}
