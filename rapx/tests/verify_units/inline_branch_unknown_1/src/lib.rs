#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[inline(never)]
fn branching_helper(input: u32) -> u32 {
    let mut value = 0;
    if input & 1 != 0 { value |= 1; }
    if input & 2 != 0 { value |= 2; }
    if input & 4 != 0 { value |= 4; }
    if input & 8 != 0 { value |= 8; }
    if input & 16 != 0 { value |= 16; }
    if input & 32 != 0 { value |= 32; }
    if input & 64 != 0 { value |= 64; }
    if input & 128 != 0 { value |= 128; }
    if input & 256 != 0 { value |= 256; }
    if input & 512 != 0 { value |= 512; }
    if input & 1024 != 0 { value |= 1024; }
    if input & 2048 != 0 { value |= 2048; }
    if input & 4096 != 0 { value |= 4096; }
    if input & 8192 != 0 { value |= 8192; }
    if input & 16384 != 0 { value |= 16384; }
    if input & 32768 != 0 { value |= 32768; }
    if input & 65536 != 0 { value |= 65536; }
    if input & 131072 != 0 { value |= 131072; }
    value
}

#[rapx::verify]
pub fn unknown_fallback_branch(input: u32) {
    let value = branching_helper(input);
    unsafe { need_nonzero(value); }
}

#[inline(never)]
fn branching_write(value: &mut u32, input: u32) {
    let mut mask = 0;
    if input & 1 != 0 { mask |= 1; }
    if input & 2 != 0 { mask |= 2; }
    if input & 4 != 0 { mask |= 4; }
    if input & 8 != 0 { mask |= 8; }
    if input & 16 != 0 { mask |= 16; }
    if input & 32 != 0 { mask |= 32; }
    if input & 64 != 0 { mask |= 64; }
    if input & 128 != 0 { mask |= 128; }
    if input & 256 != 0 { mask |= 256; }
    if input & 512 != 0 { mask |= 512; }
    if input & 1024 != 0 { mask |= 1024; }
    if input & 2048 != 0 { mask |= 2048; }
    if input & 4096 != 0 { mask |= 4096; }
    if input & 8192 != 0 { mask |= 8192; }
    if input & 16384 != 0 { mask |= 16384; }
    if input & 32768 != 0 { mask |= 32768; }
    if input & 65536 != 0 { mask |= 65536; }
    if input & 131072 != 0 { mask |= 131072; }
    if mask == 0 { *value = 0; }
}

#[rapx::verify]
pub fn unknown_fallback_write(input: u32) {
    let mut value = 1;
    branching_write(&mut value, input);
    unsafe { need_nonzero(value); }
}

#[inline(never)]
fn always_init_after_branches(out: &mut std::mem::MaybeUninit<u32>, input: u32) {
    let mut mask = 0;
    if input & 1 != 0 { mask |= 1; }
    if input & 2 != 0 { mask |= 2; }
    if input & 4 != 0 { mask |= 4; }
    if input & 8 != 0 { mask |= 8; }
    if input & 16 != 0 { mask |= 16; }
    if input & 32 != 0 { mask |= 32; }
    if input & 64 != 0 { mask |= 64; }
    if input & 128 != 0 { mask |= 128; }
    if input & 256 != 0 { mask |= 256; }
    if input & 512 != 0 { mask |= 512; }
    if input & 1024 != 0 { mask |= 1024; }
    if input & 2048 != 0 { mask |= 2048; }
    if input & 4096 != 0 { mask |= 4096; }
    if input & 8192 != 0 { mask |= 8192; }
    if input & 16384 != 0 { mask |= 16384; }
    if input & 32768 != 0 { mask |= 32768; }
    if input & 65536 != 0 { mask |= 65536; }
    if input & 131072 != 0 { mask |= 131072; }
    out.write(mask | 1);
}

#[rapx::verify]
pub fn no_false_uninit(input: u32) -> u32 {
    let mut value = std::mem::MaybeUninit::uninit();
    always_init_after_branches(&mut value, input);
    unsafe { value.assume_init() }
}

#[inline(never)]
fn maybe_init_before_overwrite(out: &mut std::mem::MaybeUninit<u32>, input: u32) {
    let mut mask = 0;
    if input & 1 != 0 { mask |= 1; }
    if input & 2 != 0 { mask |= 2; }
    if input & 4 != 0 { mask |= 4; }
    if input & 8 != 0 { mask |= 8; }
    if input & 16 != 0 { mask |= 16; }
    if input & 32 != 0 { mask |= 32; }
    if input & 64 != 0 { mask |= 64; }
    if input & 128 != 0 { mask |= 128; }
    if input & 256 != 0 { mask |= 256; }
    if input & 512 != 0 { mask |= 512; }
    if input & 1024 != 0 { mask |= 1024; }
    if input & 2048 != 0 { mask |= 2048; }
    if input & 4096 != 0 { mask |= 4096; }
    if input & 8192 != 0 { mask |= 8192; }
    if input & 16384 != 0 { mask |= 16384; }
    if input & 32768 != 0 { mask |= 32768; }
    if input & 65536 != 0 { mask |= 65536; }
    if input & 131072 != 0 { mask |= 131072; }
    if mask != 0 { out.write(mask); }
}

#[rapx::verify]
pub fn no_false_uninit_after_overwrite(input: u32) -> u32 {
    let mut value = std::mem::MaybeUninit::uninit();
    maybe_init_before_overwrite(&mut value, input);
    value.write(1);
    unsafe { value.assume_init() }
}
