#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused_variables)]

#[rapx::requires(ValidNum(value == 0))]
unsafe fn require_zero(value: u32) {}

#[rapx::verify]
pub fn copy_changes_second_element() {
    let source = [2_u32, 3];
    let mut destination = [0_u32, 0];
    unsafe {
        core::ptr::copy_nonoverlapping(source.as_ptr(), destination.as_mut_ptr(), 2);
        require_zero(destination[1]);
    }
}
