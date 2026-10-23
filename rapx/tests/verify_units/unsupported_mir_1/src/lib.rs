#![feature(register_tool, core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code, internal_features)]

use std::arch::asm;

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[rapx::verify]
pub fn unknown_inline_asm_write() {
    let mut value = 1_u32;
    unsafe { asm!("xor {reg:e}, {reg:e}", reg = inout(reg) value); }
    unsafe { need_nonzero(value); }
}

#[rapx::verify]
pub fn unknown_intrinsic_copy() {
    let source = 0_u32;
    let mut destination = 1_u32;
    unsafe { std::intrinsics::copy_nonoverlapping(&source, &mut destination, 1); }
    unsafe { need_nonzero(destination); }
}
