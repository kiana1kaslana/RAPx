#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused_variables)]

use core::{mem::MaybeUninit, ptr};

#[rapx::requires(Init(pointer, u32, count))]
unsafe fn require_init(pointer: *const u32, count: usize) {}

#[rapx::verify]
pub fn copy_symbolic_prefix(source: &[u32; 4], destination: &mut [u32; 4], count: usize) {
    let mut scratch = MaybeUninit::<([u64; 2], [u32; 0])>::uninit();
    let buffer = scratch.as_mut_ptr().cast::<u32>();
    if count <= 4 {
        unsafe {
            ptr::copy_nonoverlapping(source.as_ptr(), buffer, count);
            require_init(buffer, count);
            ptr::copy_nonoverlapping(buffer, destination.as_mut_ptr(), count);
        }
    }
}

#[rapx::verify]
pub fn copy_past_prefix(source: &[u32; 2], destination: &mut [u32; 2]) {
    let mut scratch = MaybeUninit::<([u64; 2], [u32; 0])>::uninit();
    let buffer = scratch.as_mut_ptr().cast::<u32>();
    unsafe {
        ptr::copy_nonoverlapping(source.as_ptr(), buffer, 1);
        require_init(buffer, 2);
        ptr::copy_nonoverlapping(buffer, destination.as_mut_ptr(), 2);
    }
}
