#![feature(const_destruct)]

use std::marker::Destruct;
fn drop<T: Destruct>(_: T) {}

fn main() {
    let x = (1, 2);
    drop(x);
}
