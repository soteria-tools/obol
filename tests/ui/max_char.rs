//@ obol-args=--include std::char::MAX
//@ obol-args=--include core::char::MAX
//@ obol-args=--include core::char::methods::_::MAX

fn main() {
    let _max_char = std::char::MAX;
}
