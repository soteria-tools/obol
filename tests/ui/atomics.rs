//! Atomic operations lower to compiler intrinsics whose memory-ordering argument is passed as a
//! *const generic* of the `core::intrinsics::AtomicOrdering` enum (e.g.
//! `atomic_store::<usize, AtomicOrdering::SeqCst>`). The interpreter relies on these const generics
//! being translated faithfully, so this test pins down that we parse them. The output pulls in a
//! lot of toolchain-dependent std machinery, so we only check that translation succeeds.
use std::sync::atomic::{AtomicUsize, Ordering};

pub fn main() {
    let a = AtomicUsize::new(0);
    a.store(1, Ordering::SeqCst);
    let _ = a.load(Ordering::Acquire);
    let _ = a.fetch_add(1, Ordering::Relaxed);
    let _ = a.compare_exchange(1, 2, Ordering::AcqRel, Ordering::Relaxed);
}
