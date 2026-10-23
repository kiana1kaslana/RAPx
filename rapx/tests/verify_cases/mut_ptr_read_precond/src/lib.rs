#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused_variables)]

// Regression: the builtin contract for `core::ptr::mut_ptr::read` referenced a
// nonexistent `src` parameter (copied from the free function `ptr::read`), so
// caller-side ValidPtr preconds were dropped. Reading also needs initialized
// memory, so the complete contract verifies while the missing-Init case fails.
#[rapx::verify]
#[rapx::requires(ValidPtr(ptr, u32, 1), kind = "precond")]
#[rapx::requires(Align(ptr, u32), kind = "precond")]
#[rapx::requires(Init(ptr, u32, 1), kind = "precond")]
unsafe fn read_slot(ptr: *mut u32) -> u32 {
    unsafe { ptr.read() }
}

#[rapx::verify]
#[rapx::requires(ValidPtr(ptr, u32, 1), kind = "precond")]
#[rapx::requires(Align(ptr, u32), kind = "precond")]
unsafe fn read_slot_without_init(ptr: *mut u32) -> u32 {
    unsafe { ptr.read() }
}
