//@ known-failure
//@ obol-arg=--start-from=start_from_errors::module1
//@ obol-arg=--start-from=module2
//@ obol-arg=--start-from=crate::module3
//@ obol-arg=--start-from=std::iter:once
//@ obol-arg=--start-from=std::ops::Deref::Target
//@ obol-arg=--start-from={impl crate::Type}
//@ obol-arg=--start-from={impl crate::Trait for &crate::Type}
//@ obol-arg=--start-from={impl crate::Trait for crate::MissingType}
//@ obol-arg=--start-from={impl crate::Trait<_> for _}
//@ obol-arg=--start-from={impl crate::Trait for crate::Type}::missing_method
//@ obol-arg=--start-from=crate::{impl crate::Trait for crate::Type}

mod module1 {}
mod module2 {}
mod module3 {}

struct Type;
impl Type {
    fn inherent_method() {}
}

trait Trait<T> {
    fn method();
}
impl Trait<()> for Type {
    fn method() {}
}
