struct Foo {}

impl Drop for Foo {
    fn drop(&mut self) {
        println!("Dropping Foo");
    }
}

#[allow(arithmetic_overflow)]
fn main() {
    let f = Foo {};
    let _ = 255u8 + 1;
    let f_ref = &f; // force Foo to be dropped after the overflow
}
