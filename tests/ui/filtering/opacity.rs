//@ obol-args=--include core::option
//@ obol-args=--exclude core::slice::raw::from_ref
//@ obol-args=--include test_crate::module::dont_translate_body
//@ obol-args=--opaque test_crate::module::dont_translate_body
//@ obol-args=--opaque crate::module::other_mod
//@ obol-args=--include crate::module::other_mod::_
//@ obol-args=--include core::convert::{core::convert::Into<_,_>}::into
//@ obol-args=--include core::convert::num::{core::convert::From<_,_>}
//@ obol-args=--opaque _::exclude_me
//@ obol-args=--exclude crate::invisible_mod
//@ obol-args=--exclude crate::keep_names_of_excluded
//@ obol-args=--include crate::keep_names_of_excluded::{crate::keep_names_of_excluded::Trait<_>}
// Note: we don't use the `impl Trait for T` syntax above because we can't have spaces in these
// options.

fn foo() {
    let _ = Some(0).is_some();
    let _: u64 = 42u32.into();
    let _ = std::slice::from_ref(&0);
}

mod module {
    fn dont_translate_body() {
        println!("aaa")
    }
    mod other_mod {
        fn dont_even_see_me() {}
    }
}

fn exclude_me() {}

mod invisible_mod {
    fn invisible() {}
}

mod keep_names_of_excluded {
    // We exclude this trait
    trait Trait {
        fn method();
    }

    // We want to include this impl, so we need to keep the name of the trait around.
    impl Trait for () {
        fn method() {
            let _ = 0;
        }
    }
}

struct Struct;

#[charon::opaque]
impl Struct {
    fn method() {
        let _ = 0;
    }
}

// Foreign modules can't be named or have attributes, so we can't mark them opaque.
#[charon::opaque]
extern "C" {
    fn extern_fn(x: i32);
}
