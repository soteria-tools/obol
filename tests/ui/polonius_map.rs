//@ rustc-args=-Zpolonius
//@ skip-in-ci
// Skipped in CI because hashbrown's `Group` alignment (baked into the output as `ctrl_align`) is
// SIMD-width-dependent — 8 on aarch64, 16 on x86_64 — so the snapshot can't match both the aarch64
// dev machines it's blessed on and the x86_64 CI runner.
#![allow(dead_code)]
use std::collections::HashMap;

/// The example the Rust team uses to illustrate why we need Polonius.
pub fn get_or_insert(map: &mut HashMap<u32, u32>) -> &u32 {
    match map.get(&22) {
        Some(v) => v,
        None => {
            map.insert(22, 33);
            &map[&22]
        }
    }
}
