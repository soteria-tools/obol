extern "C" {
    static mut FOO: i32;
    static BAR: Option<*const i32>;
}

fn main() {
    let foo = unsafe { FOO };
    let bar = unsafe { BAR };
}
