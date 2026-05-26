trait Ord {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering;
}

impl Ord for i32 {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

fn min<T: Ord>() {
    let _ = T::cmp;
}

fn main() {
    min::<i32>();
}
