//@ obol-args=--precise-drops
//@ obol-args=--monomorphize
//@ obol-args=--include=core::marker::Destruct
fn drop_array(_: [String; 4]) {}

fn drop_slice(_: Box<[String]>) {}

fn drop_tuple(_: (String, String)) {}
