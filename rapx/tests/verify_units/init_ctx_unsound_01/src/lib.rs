#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use std::mem::MaybeUninit;

/// # Safety
/// `ptr` must be non-null, aligned for `u32`, and point to allocated memory.
#[rapx::requires(ValidPtr(ptr, u32, 1))]
#[rapx::requires(Align(ptr, u32))]
#[rapx::verify]
unsafe fn maybe_init_slot(ptr: *mut u32, value: u32, flag: bool) {
    if flag {
        unsafe { ptr.write(value) }
    }
}

/// # Safety
/// Same as `maybe_init_slot`. Its own `flag` is ignored: the call below
/// always passes `false`, so nothing is ever written. The branch keeps the
/// VM from inlining it, so callers use its summary.
unsafe fn never_init_slot(ptr: *mut u32, value: u32, _flag: bool) {
    let value = if value > 10 { value } else { 10 };
    unsafe { maybe_init_slot(ptr, value, false) }
}

#[rapx::verify]
pub fn sound_literal_true(value: u32) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();
    unsafe { maybe_init_slot(ptr, value, true) }
    unsafe { slot.assume_init_read() }
}

// UNSOUND: the caller passes `false`, so the conditional write never fires.
#[rapx::verify]
pub fn unsound_literal_false(value: u32) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();
    unsafe { maybe_init_slot(ptr, value, false) }
    unsafe { slot.assume_init_read() }
}

// UNSOUND: `never_init_slot` always passes `false` down, regardless of `flag`.
#[rapx::verify]
pub fn unsound_wrapper_runtime_flag(value: u32, flag: bool) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();
    unsafe { never_init_slot(ptr, value, flag) }
    unsafe { slot.assume_init_read() }
}

// UNSOUND: the literal `true` at the call site is `never_init_slot`'s `_flag`,
// which is ignored. The nested summary must not fold `maybe_init_slot`'s `flag`
// (always `false`) to the caller's literal — that would prune the non-writing
// path and report the slot as initialized.
#[rapx::verify]
pub fn unsound_wrapper_literal_true(value: u32) -> u32 {
    let mut slot = MaybeUninit::<u32>::uninit();
    let ptr = slot.as_mut_ptr();
    unsafe { never_init_slot(ptr, value, true) }
    unsafe { slot.assume_init_read() }
}
