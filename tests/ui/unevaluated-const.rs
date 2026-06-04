use std::sync::atomic::AtomicU64;

const NUM_HARTS: usize = 2;
const INITIAL_STATE: AtomicU64 = AtomicU64::new(0);

static HART_STATES: [AtomicU64; NUM_HARTS] = [INITIAL_STATE; NUM_HARTS];

fn main() {
    let _x = unsafe { HART_STATES[0].load(std::sync::atomic::Ordering::Relaxed) };
}
