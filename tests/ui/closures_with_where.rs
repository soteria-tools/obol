trait Ops<const K: usize> {
    fn of_usize(x: usize) -> Self;
}

fn test<const K: usize, T: Ops<K>>() -> [T; 1] {
    core::array::from_fn(|i| T::of_usize(i))
}

impl<const K: usize> Ops<K> for [u8; 1] {
    fn of_usize(x: usize) -> Self {
        [x as u8]
    }
}

fn main() {
    let _ = test::<0, [u8; 1]>();
}
