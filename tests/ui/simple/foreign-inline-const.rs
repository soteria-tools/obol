//@ aux-crate=closure-inside-inline-const.rs

fn bar<T>() {
    closure_inside_inline_const::foo::<T>();
}
