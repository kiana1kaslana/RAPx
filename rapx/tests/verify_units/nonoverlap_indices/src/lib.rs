#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(NonOverlap(indices))]
unsafe fn use_indices(indices: [usize; 2]) {
    let _ = indices;
}

#[rapx::requires(NonOverlap(indices))]
unsafe fn use_ranges(indices: [std::ops::Range<usize>; 2]) {
    let _ = indices;
}

#[rapx::requires(NonOverlap(indices))]
unsafe fn use_inclusive_ranges(indices: [std::ops::RangeInclusive<usize>; 2]) {
    let _ = indices;
}

#[rapx::requires(NonOverlap(indices))]
unsafe fn use_generic_indices<const N: usize>(indices: [usize; N]) {
    let _ = indices;
}

#[rapx::requires(InBound(ptr, u32, count))]
unsafe fn use_array_ptr(ptr: *const u32, count: usize) {
    let _ = (ptr, count);
}


#[rapx::verify]
pub fn sound_generic_array_reference<const N: usize>(values: &[u32; N]) {
    unsafe { use_array_ptr(values.as_ptr(), N) }
}

#[rapx::verify]
pub fn unsound_generic_array_reference_extra<const N: usize>(values: &[u32; N]) {
    unsafe { use_array_ptr(values.as_ptr(), N + 1) }
}

#[rapx::verify]
pub fn sound_generic_array_value<const N: usize>(values: [u32; N]) {
    unsafe { use_array_ptr(values.as_ptr(), N) }
}

#[rapx::verify]
pub fn unsound_generic_array_value_extra<const N: usize>(values: [u32; N]) {
    unsafe { use_array_ptr(values.as_ptr(), N + 1) }
}

#[rapx::requires(NonOverlap(indices))]
unsafe fn assert_disjoint_inside(indices: [usize; 2]) {
    assert!(indices[0] != indices[1]);
}

fn choose_index(value: usize) -> usize {
    if value == 0 { 0 } else { 1 }
}

#[rapx::verify]
pub fn sound_distinct_indices() {
    unsafe { use_indices([0, 1]) }
}

#[rapx::verify]
pub fn unsound_duplicate_indices() {
    unsafe { use_indices([0, 0]) }
}

#[rapx::verify]
pub fn unsound_callee_assertion() {
    unsafe { assert_disjoint_inside([0, 0]) }
}

#[rapx::verify]
pub fn unsound_unknown_indices(indices: [usize; 2]) {
    unsafe { use_indices(indices) }
}

#[rapx::verify]
pub fn unsound_overwritten_indices(indices: [usize; 2]) {
    let mut values = [0, 1];
    values = indices;
    unsafe { use_indices(values) }
}

#[rapx::verify]
pub fn sound_guarded_indices(a: usize, b: usize) {
    if a != b {
        unsafe { use_indices([a, b]) }
    }
}

#[rapx::verify]
pub fn unsound_overwritten_duplicate() {
    let mut values = [0, 1];
    values = [0, 0];
    unsafe { use_indices(values) }
}

#[rapx::verify]
pub fn unsound_indexed_write() {
    let mut values = [0, 1];
    values[1] = 0;
    unsafe { use_indices(values) }
}

#[rapx::verify]
pub fn sound_adjacent_ranges() {
    unsafe { use_ranges([0..2, 2..4]) }
}

#[rapx::verify]
pub fn unsound_overlapping_ranges() {
    unsafe { use_ranges([0..3, 2..4]) }
}

#[rapx::verify]
pub fn unsound_range_indexed_write() {
    let mut ranges = [0..2, 2..4];
    ranges[1] = 1..3;
    unsafe { use_ranges(ranges) }
}

#[rapx::verify]
pub fn sound_empty_range_at_edge() {
    unsafe { use_ranges([0..0, 0..4]) }
}

#[rapx::verify]
pub fn unsound_empty_range_in_middle() {
    unsafe { use_ranges([2..2, 0..4]) }
}

#[rapx::verify]
pub fn sound_adjacent_inclusive_ranges() {
    unsafe { use_inclusive_ranges([0..=1, 2..=3]) }
}

#[rapx::verify]
pub fn unsound_touching_inclusive_ranges() {
    unsafe { use_inclusive_ranges([0..=2, 2..=3]) }
}

#[rapx::verify]
pub fn sound_checked_generic_indices<const N: usize>(indices: [usize; N]) {
    for i in 0..N {
        for j in 0..i {
            if indices[i] == indices[j] {
                return;
            }
        }
    }
    unsafe { use_generic_indices(indices) }
}

#[rapx::verify]
pub fn sound_checked_slice_iter_indices<const N: usize>(indices: [usize; N]) {
    for (i, idx) in indices.iter().enumerate() {
        for idx2 in &indices[..i] {
            if idx == idx2 {
                return;
            }
        }
    }
    unsafe { use_generic_indices(indices) }
}

// The opposite guard does not establish distinct indices. Until generic
// PartialEq calls can be resolved, both iterator paths must remain UNKNOWN.
#[rapx::verify]
pub fn unsound_reversed_slice_iter_guard<const N: usize>(indices: [usize; N]) {
    for (i, idx) in indices.iter().enumerate() {
        for idx2 in &indices[..i] {
            if idx != idx2 {
                return;
            }
        }
    }
    unsafe { use_generic_indices(indices) }
}

#[rapx::verify]
pub fn sound_ref_guard(a: &usize, b: &usize) {
    if a == b {
        return;
    }
    unsafe { use_indices([*a, *b]) }
}

#[rapx::verify]
pub fn unsound_reversed_ref_guard(a: &usize, b: &usize) {
    if a != b {
        return;
    }
    unsafe { use_indices([*a, *b]) }
}

#[rapx::verify]
pub fn sound_lt_ref_guard(a: &usize, b: &usize) {
    if a < b {
        unsafe { use_indices([*a, *b]) }
    }
}

#[rapx::verify]
pub fn sound_le_false_guard(a: &usize, b: &usize) {
    if a <= b {
        return;
    }
    unsafe { use_indices([*a, *b]) }
}

#[rapx::verify]
pub fn sound_gt_ref_guard(a: &usize, b: &usize) {
    if a > b {
        unsafe { use_indices([*a, *b]) }
    }
}

#[rapx::verify]
pub fn sound_ge_false_guard(a: &usize, b: &usize) {
    if a >= b {
        return;
    }
    unsafe { use_indices([*a, *b]) }
}

#[rapx::verify]
pub fn unsound_le_ref_guard(a: &usize, b: &usize) {
    if a <= b {
        unsafe { use_indices([*a, *b]) }
    }
}

#[rapx::verify]
pub fn unsound_ge_ref_guard(a: &usize, b: &usize) {
    if a >= b {
        unsafe { use_indices([*a, *b]) }
    }
}

#[rapx::verify]
pub fn unsound_lt_false_guard(a: &usize, b: &usize) {
    if a < b {
        return;
    }
    unsafe { use_indices([*a, *b]) }
}

#[rapx::verify]
pub fn unsound_gt_false_guard(a: &usize, b: &usize) {
    if a > b {
        return;
    }
    unsafe { use_indices([*a, *b]) }
}

#[rapx::verify]
pub fn sound_empty_inner_iterator<const N: usize>(indices: [usize; N]) {
    for _ in &indices[..0] {
        unsafe { use_generic_indices(indices) }
    }
}

#[rapx::verify]
pub fn sound_enumerate_second_index() {
    let indices = [0usize, 1];
    let mut iter = indices.iter().enumerate();
    let _ = iter.next();
    if let Some((index, _)) = iter.next() {
        unsafe { use_indices([0, index]) }
    }
}

#[rapx::verify]
pub fn sound_independent_iterators() {
    let values = [0, 1];
    let mut first = values.iter();
    let mut second = values.iter();
    first.next();
    if let (Some(left), Some(right)) = (first.next(), second.next()) {
        unsafe { use_indices([*left, *right]) }
    }
}

#[rapx::verify]
pub fn unsound_independent_iterators() {
    let values = [0, 1];
    let mut first = values.iter();
    let mut second = values.iter();
    first.next();
    if let (Some(_left), Some(right)) = (first.next(), second.next()) {
        unsafe { use_indices([*right, 0]) }
    }
}

#[rapx::verify]
pub fn sound_moved_iterator() {
    let values = [0, 1];
    let mut iter = values.iter();
    iter.next();
    let mut moved = iter;
    if let Some(value) = moved.next() {
        unsafe { use_indices([0, *value]) }
    }
}

struct Counter {
    value: usize,
}

fn increment(counter: &mut Counter) {
    counter.value += 1;
}

#[rapx::verify]
pub fn sound_inline_field_update() {
    let mut counter = Counter { value: 0 };
    increment(&mut counter);
    unsafe { use_indices([0, counter.value]) }
}

#[rapx::verify]
pub fn unsound_inline_field_update() {
    let mut counter = Counter { value: 0 };
    increment(&mut counter);
    unsafe { use_indices([1, counter.value]) }
}

#[rapx::verify]
pub fn sound_at_most_one_generic_index<const N: usize>(indices: [usize; N]) {
    if N <= 1 {
        unsafe { use_generic_indices(indices) }
    }
}

#[rapx::verify]
pub fn sound_range_next_indices() {
    let mut range = 0..2;
    if let (Some(first), Some(second)) = (range.next(), range.next()) {
        unsafe { use_indices([first, second]) }
    }
}

#[rapx::verify]
pub fn sound_range_next_symbolic(start: usize, end: usize) {
    let mut range = start..end;
    if let (Some(first), Some(second)) = (range.next(), range.next()) {
        unsafe { use_indices([first, second]) }
    }
}

#[rapx::verify]
pub fn sound_iter_next_indices() {
    let values = [0usize, 1];
    let mut iter = values.iter();
    if let (Some(first), Some(second)) = (iter.next(), iter.next()) {
        unsafe { use_indices([*first, *second]) }
    }
}

#[rapx::verify]
pub fn unsound_iter_next_duplicate() {
    let values = [0usize, 0];
    let mut iter = values.iter();
    if let (Some(first), Some(second)) = (iter.next(), iter.next()) {
        unsafe { use_indices([*first, *second]) }
    }
}

#[rapx::verify]
pub fn unsound_iter_next_after_write() {
    let mut values = [0usize, 1];
    values[1] = 0;
    let mut iter = values.iter();
    if let (Some(first), Some(second)) = (iter.next(), iter.next()) {
        unsafe { use_indices([*first, *second]) }
    }
}

#[rapx::verify]
pub fn unsound_range_next_duplicate() {
    let mut range = 0..2;
    if let Some(first) = range.next() {
        unsafe { use_indices([first, first]) }
    }
}

#[rapx::verify]
pub fn unsound_branchy_duplicate(value: usize) {
    let index = choose_index(value);
    unsafe { use_indices([index, index]) }
}
