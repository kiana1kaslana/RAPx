#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::invariant(Pinned(ptr, tag))]
pub struct Holder {
    ptr: *const u8,
}

impl Holder {
    #[rapx::verify]
    pub fn inspect(&self) -> usize {
        self.ptr as usize
    }
}
