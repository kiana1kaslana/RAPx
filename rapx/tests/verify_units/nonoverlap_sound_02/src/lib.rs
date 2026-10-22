#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code, unused_assignments)]

#[rapx::verify]
pub fn sound_copy_nonoverlapping_disjoint(data: &mut [u32; 4]) {
    let src = data.as_ptr();
    let dst = unsafe { data.as_mut_ptr().add(2) };
    unsafe {
        std::ptr::copy_nonoverlapping(src, dst, 2);
    }
}

#[rapx::verify]
pub fn sound_zero_copy_same_pointer() {
    let mut value = 1u32;
    let ptr = &mut value as *mut u32;
    unsafe { std::ptr::copy_nonoverlapping(ptr, ptr, 0) };
}

#[rapx::verify]
pub fn sound_symbolic_disjoint_copy(data: &mut [u32; 4], n: usize) {
    if n <= 2 {
        let src = data.as_ptr();
        let dst = unsafe { data.as_mut_ptr().add(2) };
        unsafe { std::ptr::copy_nonoverlapping(src, dst, n) };
    }
}
