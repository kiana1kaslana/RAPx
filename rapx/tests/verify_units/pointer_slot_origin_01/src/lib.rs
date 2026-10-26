#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::requires(Allocated(pointer, u32, 1), kind = "precond")]
unsafe fn require_allocated(pointer: *mut u32) {
    let _ = pointer;
}

#[rapx::requires(ValidNum(value == 7), kind = "precond")]
unsafe fn require_seven(value: u8) {
    let _ = value;
}

struct Bucket {
    slots: Box<[*mut u32; 2]>,
}

struct NestedBucket {
    rows: Box<[[*mut u32; 2]; 2]>,
}

struct InnerPointer {
    pointer: *mut u32,
}

struct OuterPointer {
    inner: InnerPointer,
}

#[repr(C)]
struct ScalarPair {
    first: u8,
    second: u8,
}

struct ScalarWrapper {
    inner: ScalarPair,
}

#[inline(never)]
fn replace_scalar_pair(pair: &mut ScalarPair, value: u8) {
    *pair = ScalarPair {
        first: value,
        second: value,
    };
}

#[inline(never)]
fn replace_wrapper_inner(wrapper: &mut ScalarWrapper, value: u8) {
    wrapper.inner = ScalarPair {
        first: value,
        second: value,
    };
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
pub fn sound_guarded_pointer_slot_read(item: &mut u32, index: usize) {
    let mut slots = [std::ptr::null_mut(); 2];
    slots[0] = item as *mut u32;
    if index == 0 {
        unsafe { require_allocated(slots[index]) };
    }
}

#[rapx::verify]
pub fn unsound_guarded_pointer_slot_read(item: &mut u32, index: usize) {
    let mut slots = [std::ptr::null_mut(); 2];
    slots[0] = item as *mut u32;
    if index == 1 {
        unsafe { require_allocated(slots[index]) };
    }
}

#[rapx::verify]
pub fn unsound_raw_pointer_slot_write(item: &mut u32) {
    let mut slots = [item as *mut u32];
    let first = slots.as_mut_ptr();
    unsafe {
        *first = std::ptr::null_mut();
        require_allocated(slots[0]);
    }
}

#[rapx::verify]
pub fn sound_pointer_slot_raw_write(item: &mut u32) {
    let mut slots = [std::ptr::null_mut()];
    let first = slots.as_mut_ptr();
    unsafe {
        *first = item as *mut u32;
        require_allocated(slots[0]);
    }
}

#[rapx::verify]
pub fn sound_distinct_symbolic_slot_write(item: &mut u32, index: usize) {
    let mut slots = [std::ptr::null_mut(); 2];
    slots[0] = item as *mut u32;
    if index == 1 {
        slots[index] = std::ptr::null_mut();
        unsafe { require_allocated(slots[0]) };
    }
}

#[rapx::verify]
pub fn sound_nested_pointer_slot(item: &mut u32) {
    let mut rows = [[std::ptr::null_mut(); 2]; 2];
    rows[1][0] = item as *mut u32;
    unsafe { require_allocated(rows[1][0]) };
}

#[rapx::verify]
pub fn sound_nested_repeated_pointer_slot(item: &mut u32) {
    let pointer = item as *mut u32;
    let rows = [[pointer; 2]; 2];
    unsafe { require_allocated(rows[1][0]) };
}

#[rapx::verify]
pub fn sound_nested_guarded_pointer_slot(item: &mut u32, index: usize) {
    let mut rows = [[std::ptr::null_mut(); 2]; 2];
    rows[1][0] = item as *mut u32;
    if index == 1 {
        unsafe { require_allocated(rows[index][0]) };
    }
}

#[rapx::verify]
pub fn sound_nested_guarded_both_indices(item: &mut u32, row: usize, column: usize) {
    let mut rows = [[std::ptr::null_mut(); 2]; 2];
    rows[1][0] = item as *mut u32;
    if row == 1 && column == 0 {
        unsafe { require_allocated(rows[row][column]) };
    }
}

#[rapx::verify]
pub fn sound_nested_distinct_column_write(item: &mut u32, column: usize) {
    let mut rows = [[std::ptr::null_mut(); 2]; 2];
    rows[1][0] = item as *mut u32;
    if column == 1 {
        rows[1][column] = std::ptr::null_mut();
        unsafe { require_allocated(rows[1][0]) };
    }
}

#[rapx::verify]
pub fn sound_three_dimensional_pointer_slot(item: &mut u32) {
    let mut blocks = [[[std::ptr::null_mut(); 2]; 2]; 2];
    blocks[1][0][1] = item as *mut u32;
    unsafe { require_allocated(blocks[1][0][1]) };
}

#[rapx::verify]
pub fn sound_boxed_nested_pointer_slot(item: &mut u32) {
    let mut bucket = NestedBucket {
        rows: Box::new([[std::ptr::null_mut(); 2]; 2]),
    };
    bucket.rows[1][0] = item as *mut u32;
    unsafe { require_allocated(bucket.rows[1][0]) };
}

#[rapx::verify]
pub fn sound_nested_other_row_reassigned(item: &mut u32) {
    let mut rows = [[std::ptr::null_mut(); 2]; 2];
    rows[0][0] = item as *mut u32;
    rows[1] = [std::ptr::null_mut(); 2];
    unsafe { require_allocated(rows[0][0]) };
}

#[rapx::verify]
pub fn sound_nested_scalar_write() {
    let mut rows = [[0u8; 2]; 2];
    rows[1][0] = 7;
    unsafe { require_seven(rows[1][0]) };
}

#[rapx::verify]
pub fn sound_nested_scalar_initial() {
    let rows = [[7u8; 2]; 2];
    unsafe { require_seven(rows[1][0]) };
}

#[rapx::verify]
pub fn sound_nested_scalar_guarded(row: usize, column: usize) {
    let mut rows = [[0u8; 2]; 2];
    rows[1][0] = 7;
    if row == 1 && column == 0 {
        unsafe { require_seven(rows[row][column]) };
    }
}

#[rapx::verify]
pub fn sound_raw_scalar_array_write() {
    let mut values = [0u8; 2];
    let pointer = values.as_mut_ptr();
    unsafe {
        *pointer.add(1) = 7;
        require_seven(values[1]);
    }
}

#[rapx::verify]
pub fn unsound_raw_scalar_array_write() {
    let mut values = [7u8; 2];
    let pointer = values.as_mut_ptr();
    unsafe {
        *pointer.add(1) = 0;
        require_seven(values[1]);
    }
}

#[rapx::verify]
pub fn sound_raw_struct_field_write() {
    let mut pair = ScalarPair { first: 0, second: 0 };
    let pointer = &raw mut pair.second;
    unsafe {
        *pointer = 7;
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn sound_raw_struct_field_preserves_sibling() {
    let mut pair = ScalarPair { first: 7, second: 0 };
    let pointer = &raw mut pair.second;
    unsafe {
        *pointer = 7;
        require_seven(pair.first);
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn unsound_raw_struct_field_write() {
    let mut pair = ScalarPair { first: 0, second: 7 };
    let pointer = &raw mut pair.second;
    unsafe {
        *pointer = 0;
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn sound_raw_boxed_struct_field_write() {
    let mut pair = Box::new(ScalarPair { first: 0, second: 0 });
    let pointer = &raw mut pair.second;
    unsafe {
        *pointer = 7;
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn unsound_raw_boxed_struct_field_write() {
    let mut pair = Box::new(ScalarPair { first: 0, second: 7 });
    let pointer = &raw mut pair.second;
    unsafe {
        *pointer = 0;
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn sound_raw_borrowed_struct_field_write(pair: &mut ScalarPair) {
    let pointer = &raw mut pair.second;
    unsafe {
        *pointer = 7;
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn unsound_raw_borrowed_struct_field_write(pair: &mut ScalarPair) {
    let pointer = &raw mut pair.second;
    unsafe {
        *pointer = 0;
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn sound_exposed_struct_field_write() {
    let mut pair = ScalarPair { first: 0, second: 0 };
    let original = &raw mut pair.second;
    let address = original.expose_provenance();
    let reconstructed = std::ptr::with_exposed_provenance_mut::<u8>(address);
    unsafe {
        *reconstructed = 7;
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn unsound_exposed_struct_field_write() {
    let mut pair = ScalarPair { first: 0, second: 7 };
    let original = &raw mut pair.second;
    let address = original.expose_provenance();
    let reconstructed = std::ptr::with_exposed_provenance_mut::<u8>(address);
    unsafe {
        *reconstructed = 0;
        require_seven(pair.second);
    }
}

#[rapx::verify]
#[rapx::requires(Allocated(first, u8, 1), kind = "precond")]
#[rapx::requires(Allocated(second, u8, 1), kind = "precond")]
pub unsafe fn unsound_aliased_raw_parameters(first: *mut u8, second: *mut u8) {
    unsafe {
        *first = 7;
        *second = 0;
        require_seven(*first);
    }
}

#[rapx::verify]
pub fn sound_exposed_transmuted_field_write() {
    let mut pair = ScalarPair { first: 0, second: 0 };
    let original = &raw mut pair.second;
    let address = original.expose_provenance();
    let reconstructed: *mut u8 = unsafe { std::mem::transmute(address) };
    unsafe {
        *reconstructed = 7;
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn unsound_exposed_transmuted_field_write() {
    let mut pair = ScalarPair { first: 0, second: 7 };
    let original = &raw mut pair.second;
    let address = original.expose_provenance();
    let reconstructed: *mut u8 = unsafe { std::mem::transmute(address) };
    unsafe {
        *reconstructed = 0;
        require_seven(pair.second);
    }
}

#[rapx::verify]
pub fn sound_replaced_pair_in_helper() {
    let mut pair = ScalarPair { first: 0, second: 0 };
    replace_scalar_pair(&mut pair, 7);
    unsafe { require_seven(pair.first) };
}

#[rapx::verify]
pub fn unsound_replaced_pair_in_helper() {
    let mut pair = ScalarPair { first: 7, second: 7 };
    replace_scalar_pair(&mut pair, 0);
    unsafe { require_seven(pair.first) };
}

#[rapx::verify]
pub fn sound_replaced_inner_in_helper() {
    let mut wrapper = ScalarWrapper {
        inner: ScalarPair { first: 0, second: 0 },
    };
    replace_wrapper_inner(&mut wrapper, 7);
    unsafe { require_seven(wrapper.inner.first) };
}

#[rapx::verify]
pub fn unsound_replaced_inner_in_helper() {
    let mut wrapper = ScalarWrapper {
        inner: ScalarPair { first: 7, second: 7 },
    };
    replace_wrapper_inner(&mut wrapper, 0);
    unsafe { require_seven(wrapper.inner.first) };
}

#[rapx::verify]
pub fn sound_replaced_struct_field(item: &mut u32) {
    let mut outer = OuterPointer {
        inner: InnerPointer {
            pointer: std::ptr::null_mut(),
        },
    };
    outer.inner = InnerPointer {
        pointer: item as *mut u32,
    };
    unsafe { require_allocated(outer.inner.pointer) };
}

#[rapx::verify]
pub fn unsound_replaced_struct_field(item: &mut u32) {
    let mut outer = OuterPointer {
        inner: InnerPointer {
            pointer: item as *mut u32,
        },
    };
    outer.inner = InnerPointer {
        pointer: std::ptr::null_mut(),
    };
    unsafe { require_allocated(outer.inner.pointer) };
}

#[rapx::verify]
pub fn sound_replaced_whole_struct(item: &mut u32) {
    let mut outer = OuterPointer {
        inner: InnerPointer {
            pointer: std::ptr::null_mut(),
        },
    };
    outer = OuterPointer {
        inner: InnerPointer {
            pointer: item as *mut u32,
        },
    };
    unsafe { require_allocated(outer.inner.pointer) };
}

#[rapx::verify]
pub fn unsound_replaced_whole_struct(item: &mut u32) {
    let mut outer = OuterPointer {
        inner: InnerPointer {
            pointer: item as *mut u32,
        },
    };
    outer = OuterPointer {
        inner: InnerPointer {
            pointer: std::ptr::null_mut(),
        },
    };
    unsafe { require_allocated(outer.inner.pointer) };
}

#[rapx::verify]
pub fn unsound_nested_scalar_overwrite() {
    let mut rows = [[0u8; 2]; 2];
    rows[1][0] = 7;
    rows[1][0] = 0;
    unsafe { require_seven(rows[1][0]) };
}

#[rapx::verify]
pub fn unsound_nested_scalar_row_reassigned() {
    let mut rows = [[0u8; 2]; 2];
    rows[1][0] = 7;
    rows[1] = [0u8; 2];
    unsafe { require_seven(rows[1][0]) };
}

#[rapx::verify]
pub fn unsound_nested_scalar_array_reassigned() {
    let mut rows = [[0u8; 2]; 2];
    rows[1][0] = 7;
    rows = [[0u8; 2]; 2];
    unsafe { require_seven(rows[1][0]) };
}

#[rapx::verify]
pub fn unsound_nested_pointer_slot(item: &mut u32) {
    let mut rows = [[std::ptr::null_mut(); 2]; 2];
    rows[1][0] = item as *mut u32;
    rows[1][0] = std::ptr::null_mut();
    unsafe { require_allocated(rows[1][0]) };
}

#[rapx::verify]
pub fn unsound_nested_other_row(item: &mut u32) {
    let mut rows = [[std::ptr::null_mut(); 2]; 2];
    rows[1][0] = item as *mut u32;
    unsafe { require_allocated(rows[0][0]) };
}

#[rapx::verify]
pub fn unsound_nested_row_reassigned(item: &mut u32) {
    let mut rows = [[std::ptr::null_mut(); 2]; 2];
    rows[1][0] = item as *mut u32;
    rows[1] = [std::ptr::null_mut(); 2];
    unsafe { require_allocated(rows[1][0]) };
}

#[rapx::verify]
pub fn unsound_nested_array_reassigned(item: &mut u32) {
    let mut rows = [[std::ptr::null_mut(); 2]; 2];
    rows[1][0] = item as *mut u32;
    rows = [[std::ptr::null_mut(); 2]; 2];
    unsafe { require_allocated(rows[1][0]) };
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
