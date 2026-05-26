//@ obol-arg=--start-from=crate::module1
//@ obol-arg=--start-from=test_crate::module2
//@ obol-arg=--start-from=std::iter::once
//@ obol-arg=--start-from=std::clone::Clone::clone_from
//@ obol-arg=--start-from=std::slice::Iter::as_slice
//@ obol-arg=--start-from=u32::wrapping_add
//@ obol-arg=--start-from=crate::*::do_translate_glob
//@ obol-arg=--start-from={impl crate::hidden_module::Trait1 for crate::hidden_module::Type1}::method
//@ obol-arg=--start-from={impl crate::hidden_module::Trait2 for _}

fn dont_translate() {}

mod module1 {
    fn do_translate() {}
    fn do_translate_glob() {}
}
mod module2 {
    fn do_translate() {}
    fn do_translate_glob() {}
}
mod hidden_module {
    fn dont_translate() {}
    fn do_translate_glob() {}

    struct Type1;
    struct Type2;
    trait Trait1 {
        fn method();
    }
    impl Trait1 for Type1 {
        fn method() {}
    }
    impl Trait1 for Type2 {
        fn method() {
            println!("don't translate this!")
        }
    }
    trait Trait2 {}
    impl Trait2 for Type1 {}
}
