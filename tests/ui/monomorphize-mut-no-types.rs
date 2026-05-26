//@ obol-arg=--monomorphize-mut=except-types
//@ obol-arg=--remove-adt-clauses
//@ obol-args=--remove-associated-types=*

fn identity<T>(x: T) -> T {
    x
}
fn use_id_mut<X, A>(mut x: A) {
    let _ = identity(&0u32);
    let _ = identity(&mut 0u32);
    let _ = identity(Some(&mut 0u32));
    let _ = identity(Some(Some(&mut x)));
}
