#![feature(register_tool, thread_local, unsafe_binders)]
#![register_tool(rapx)]
#![allow(dead_code, incomplete_features, unused_variables)]

#[thread_local]
static TLS: u32 = 7;

#[rapx::requires(NonNull(ptr))]
unsafe fn need_nonnull(ptr: *const u32) {}

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[rapx::verify]
pub fn sound_thread_local_ref() {
    unsafe { need_nonnull(&raw const TLS) };
}

#[rapx::verify]
pub fn sound_wrap_unsafe_binder() {
    let value = 7;
    let wrapped: unsafe<'a> &'a u32 = unsafe { core::unsafe_binder::wrap_binder!(&value) };
    let unwrapped = unsafe { core::unsafe_binder::unwrap_binder!(wrapped) };
    unsafe { need_nonzero(*unwrapped) };
}

#[rapx::verify]
pub fn unsound_wrap_unsafe_binder() {
    let value = 0;
    let wrapped: unsafe<'a> &'a u32 = unsafe { core::unsafe_binder::wrap_binder!(&value) };
    let unwrapped = unsafe { core::unsafe_binder::unwrap_binder!(wrapped) };
    unsafe { need_nonzero(*unwrapped) };
}

#[rapx::verify]
pub fn unsound_scalar_deref_zero() {
    let value = 0;
    let ptr = &value;
    unsafe { need_nonzero(*ptr) };
}
