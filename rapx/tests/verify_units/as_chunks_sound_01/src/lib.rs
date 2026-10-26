#![feature(register_tool)]
#![feature(core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code)]

// SOUND: `N` is a nonzero const generic and the path guard proves exact division.
#[rapx::verify]
pub fn sound_as_chunks_unchecked_exact_div(data: &[u32]) -> usize {
    if data.len() % 4 == 0 {
        let chunks = unsafe { data.as_chunks_unchecked::<4>() };
        chunks.len()
    } else {
        0
    }
}

// SOUND: `exact_div` is guarded by the same divisor and divisibility condition.
#[rapx::verify]
pub fn sound_exact_div_guard(data: &[u32]) -> usize {
    if data.len() % 4 == 0 {
        unsafe { core::intrinsics::exact_div(data.len(), 4) }
    } else {
        0
    }
}

#[rapx::verify]
pub fn sound_generic_exact_div<const N: usize>(data: &[u32]) -> usize {
    if N == 0 {
        return 0;
    }
    if data.len() % N == 0 {
        unsafe { core::intrinsics::exact_div(data.len(), N) }
    } else {
        0
    }
}

#[rapx::verify]
pub fn sound_generic_as_chunks<const N: usize>(data: &[u32]) -> usize {
    if N == 0 {
        return 0;
    }
    if data.len() % N == 0 {
        unsafe { data.as_chunks_unchecked::<N>() }.len()
    } else {
        0
    }
}

#[rapx::verify]
#[rapx::requires(ValidNum(N, "[1,)"))]
#[rapx::requires(ValidNum(len(data) % N == 0))]
pub unsafe fn sound_generic_exact_div_requires<const N: usize>(data: &[u32]) -> usize {
    unsafe { core::intrinsics::exact_div(data.len(), N) }
}

#[rapx::verify]
pub fn sound_non_zst_flat_len<T, const N: usize>(data: &[[T; N]]) -> usize {
    if core::mem::size_of::<T>() == 0 {
        return 0;
    }
    unsafe { data.len().unchecked_mul(N) }
}

#[rapx::verify]
pub fn sound_non_zst_flatten<T, const N: usize>(data: &[[T; N]]) -> Option<&[T]> {
    if core::mem::size_of::<T>() == 0 {
        return None;
    }
    let len = unsafe { data.len().unchecked_mul(N) };
    Some(unsafe { core::slice::from_raw_parts(data.as_ptr().cast(), len) })
}
