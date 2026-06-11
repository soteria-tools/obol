//@ output=pretty-llbc
//! Named (top-level and associated) const items are translated as `GlobalKind::NamedConst`
//! globals and *referenced* from the code that uses them, rather than being inlined as anonymous
//! consts. Associated/generic consts get their generic arguments appended to the name so distinct
//! monomorphizations stay distinct (e.g. `LEN::<u8>` vs `LEN::<u32>`).
const A: u32 = 42;

const ARR: [u32; 3] = [1, 2, 3];

trait HasLen {
    const LEN: usize;
}

impl HasLen for u8 {
    const LEN: usize = 1;
}

impl HasLen for u32 {
    const LEN: usize = 4;
}

pub fn get_a() -> u32 {
    A
}

pub fn get_arr() -> [u32; 3] {
    ARR
}

pub fn lens() -> usize {
    <u8 as HasLen>::LEN + <u32 as HasLen>::LEN
}
