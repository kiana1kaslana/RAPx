#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]
#![allow(unused_variables)]

// Regression: MaybeUninit::uninit storage was marked initialized at creation
// (offset-0 return inference + plain stores), so a read that skips the only
// write verified as SOUND. The read is UB on the skip path; verify must
// report UNSOUND.
#[rapx::verify]
unsafe fn probe(flag: bool) -> u32 {
    let mut slot = std::mem::MaybeUninit::<u32>::uninit();
    let p = slot.as_mut_ptr();
    if flag {
        unsafe { p.write(1) };
    }
    unsafe { p.read() }
}
