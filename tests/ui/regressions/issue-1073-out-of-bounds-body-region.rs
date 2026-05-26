use std::io::IoSlice;

pub fn foo(bufs: &mut &mut [IoSlice<'_>]) {
    IoSlice::advance_slices(bufs, 0);
}
