//@ no-check-output
//! Limitation regression test: the constant translator reads scalar values
//! byte-by-byte and bails with `Found uninitialized bytes when reading ...` when
//! a scalar's backing allocation is only partially initialized. The standard
//! library's thread-local lazy-init state (pulled in by `thread::spawn`) is one
//! such constant. obol must drop the offending global gracefully and still exit
//! successfully; it must not panic.
//!
//! Output is not checked because the failing item's name embeds unstable
//! allocation/type ids; this test only guards against a regression to a hard
//! crash.
pub fn spawn_and_join() -> i32 {
    let handle = std::thread::spawn(|| 41 + 1);
    handle.join().unwrap()
}
