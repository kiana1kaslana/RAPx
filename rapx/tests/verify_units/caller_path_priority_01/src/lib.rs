#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[inline]
fn branchy(input: u32) -> u32 {
    let mut value = input;
    if input & 1 != 0 { value ^= 1; }
    if input & 2 != 0 { value ^= 2; }
    if input & 4 != 0 { value ^= 4; }
    if input & 8 != 0 { value ^= 8; }
    if input & 16 != 0 { value ^= 16; }
    if input & 32 != 0 { value ^= 32; }
    if input & 64 != 0 { value ^= 64; }
    if input & 128 != 0 { value ^= 128; }
    value | 1
}

#[inline]
fn branchy_other(input: u32) -> u32 {
    let mut value = input;
    if input & 1 != 0 { value ^= 256; }
    if input & 2 != 0 { value ^= 512; }
    if input & 4 != 0 { value ^= 1024; }
    if input & 8 != 0 { value ^= 2048; }
    if input & 16 != 0 { value ^= 4096; }
    if input & 32 != 0 { value ^= 8192; }
    if input & 64 != 0 { value ^= 16384; }
    if input & 128 != 0 { value ^= 32768; }
    value
}

#[rapx::verify]
pub fn caller_branch_after_helper(input: u32, choose_helper: bool) {
    if choose_helper {
        let value = branchy(input);
        unsafe { need_nonzero(value); }
    } else {
        let value = branchy_other(input);
        unsafe { need_nonzero(value & 0); }
    }
}

#[rapx::verify]
pub fn sound_unreachable_branch(input: u32) {
    if input == 0 {
        if input != 0 {
            unsafe { need_nonzero(0); }
        }
    }
}
