const SOME_INT: &&i32 = &&0;

fn main() {
    assert!(**SOME_INT == 0);
}
