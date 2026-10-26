#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::verify]
pub fn copy_uninit_into_slice(dst: &mut [u32]) {
    if dst.is_empty() {
        return;
    }
    let source = core::mem::MaybeUninit::<u32>::uninit();
    unsafe {
        core::ptr::copy_nonoverlapping(source.as_ptr(), dst.as_mut_ptr(), 1);
    }
}
