//@ obol-args=--precise-drops
//@ obol-args=--desugar-drops
//@ obol-args=--include=alloc::string::String
fn use_string(_: String) {}

fn main() {
    let _s = String::new();
}
