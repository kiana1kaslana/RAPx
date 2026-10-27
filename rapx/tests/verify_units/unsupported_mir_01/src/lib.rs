#![feature(register_tool, core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code, internal_features)]

use std::arch::asm;

unsafe extern "C" {
    safe fn external_clobber(value: &mut u32);
}

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[rapx::requires(Allocated(pointer, u32, 1))]
unsafe fn need_allocated(pointer: *const u32) {}

#[rapx::verify]
pub fn unknown_inline_asm_write() {
    let mut value = 1_u32;
    unsafe { asm!("xor {reg:e}, {reg:e}", reg = inout(reg) value); }
    unsafe { need_nonzero(value); }
}

#[rapx::verify]
pub fn unknown_external_call_without_mir() {
    let mut value = 1_u32;
    external_clobber(&mut value);
    unsafe { need_nonzero(value); }
}

#[rapx::verify]
pub fn unknown_fnmut_writes_argument<F: FnMut(&mut u32)>(mut callback: F) {
    let mut value = 1_u32;
    callback(&mut value);
    unsafe { need_nonzero(value); }
}

#[rapx::verify]
pub fn callback_bool_may_zero_argument<F: FnMut(&mut u32) -> bool>(mut callback: F) {
    let mut value = 1_u32;
    let _ = callback(&mut value);
    unsafe { need_nonzero(value); }
}

#[rapx::verify]
pub fn callback_bool_preserves_private_local<F: FnMut(&u32) -> bool>(mut callback: F) {
    let value = 1_u32;
    let other = 2_u32;
    let _ = callback(&other);
    unsafe { need_nonzero(value); }
}

#[rapx::requires(Allocated(pointer, u32, 1), kind = "precond")]
#[rapx::verify]
pub unsafe fn callback_may_drop_unborrowed<F: FnMut() -> bool>(
    pointer: *const u32,
    mut callback: F,
) {
    let _ = callback();
    unsafe { need_allocated(pointer); }
}

#[rapx::verify]
pub fn unsound_intrinsic_copy() {
    let source = 0_u32;
    let mut destination = 1_u32;
    unsafe { std::intrinsics::copy_nonoverlapping(&source, &mut destination, 1); }
    unsafe { need_nonzero(destination); }
}

#[rapx::verify]
pub unsafe fn unknown_direct_intrinsic_copy(pointer: *mut u32) {
    unsafe { std::intrinsics::copy_nonoverlapping(pointer, pointer, 1) };
}

#[rapx::verify]
pub unsafe fn unknown_direct_assume() {
    unsafe { std::intrinsics::assume(false) };
}
