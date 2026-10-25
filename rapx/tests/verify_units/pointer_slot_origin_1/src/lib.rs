#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::requires(Allocated(pointer, u32, 1), kind = "precond")]
unsafe fn require_allocated(pointer: *mut u32) {
    let _ = pointer;
}

struct Bucket {
    slots: Box<[*mut u32; 2]>,
}

#[rapx::invariant(Allocated(slots.iter(), u32, 1))]
struct InvalidBucket {
    slots: Box<[*mut u32; 1]>,
}

#[rapx::verify]
pub fn sound_pointer_slot_roundtrip(item: &mut u32, index: usize) {
    let mut slots = [std::ptr::null_mut(); 2];
    if index < slots.len() {
        slots[index] = item as *mut u32;
        let loaded = slots[index];
        unsafe { require_allocated(loaded) };
    }
}

#[rapx::verify]
pub fn sound_boxed_pointer_slot_roundtrip(item: &mut u32, index: usize) {
    let mut bucket = Bucket {
        slots: Box::new([std::ptr::null_mut(); 2]),
    };
    if index < bucket.slots.len() {
        bucket.slots[index] = item as *mut u32;
        let loaded = bucket.slots[index];
        unsafe { require_allocated(loaded) };
    }
}

#[rapx::verify]
pub fn unsound_pointer_slot_overwrite(pointer: *mut u32) {
    let mut slots = [pointer];
    slots[0] = std::ptr::null_mut();
    unsafe { require_allocated(slots[0]) };
}

#[rapx::verify]
pub fn unsound_pointer_array_reassigned(pointer: *mut u32) {
    let mut slots = [pointer];
    slots[0] = pointer;
    slots = [std::ptr::null_mut()];
    unsafe { require_allocated(slots[0]) };
}

#[rapx::verify]
pub fn unknown_external_pointer_slot(slots: &[*mut u32], index: usize) {
    if index < slots.len() {
        let loaded = slots[index];
        unsafe { require_allocated(loaded) };
    }
}

#[rapx::verify]
pub fn unsound_pointer_array_alias_overwrite(pointer: *mut u32, index: usize) {
    let mut slots = [pointer; 2];
    if index < slots.len() {
        slots[index] = pointer;
        let alias = &mut slots;
        *alias = [std::ptr::null_mut(); 2];
        unsafe { require_allocated(slots[index]) };
    }
}

impl InvalidBucket {
    #[rapx::verify]
    pub fn new() -> Self {
        Self {
            slots: Box::new([std::ptr::null_mut()]),
        }
    }
}
