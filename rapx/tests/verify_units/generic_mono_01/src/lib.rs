#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonNull(_ptr), kind = "precond")]
unsafe fn require_nonnull(_ptr: *const u8) {}

// A single-trait bound so the generic caller is monomorphized per impl.
pub trait PtrSource {
    fn ptr(&self) -> *const u8;
}

struct Dangling;
impl PtrSource for Dangling {
    fn ptr(&self) -> *const u8 {
        std::ptr::NonNull::<u8>::dangling().as_ptr()
    }
}

struct Null;
impl PtrSource for Null {
    fn ptr(&self) -> *const u8 {
        std::ptr::null()
    }
}

// Monomorphized per `PtrSource` impl:
//   I = Dangling  -> inlined `dangling()` -> NonNull proved (SOUND)
//   I = Null      -> inlined `null()`     -> NonNull fails (UNSOUND)
#[rapx::verify]
pub fn generic_ptr<I: PtrSource>(x: &I) {
    let p = x.ptr();
    unsafe {
        require_nonnull(p);
    }
}
