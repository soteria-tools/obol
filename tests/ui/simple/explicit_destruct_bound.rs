//@ known-failure

#![feature(const_destruct)]

use std::marker::Destruct;
fn drop<T: Destruct>(_: T) {}
