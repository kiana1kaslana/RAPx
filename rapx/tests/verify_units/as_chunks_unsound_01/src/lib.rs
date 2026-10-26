#![feature(register_tool)]
#![feature(core_intrinsics)]
#![register_tool(rapx)]
#![allow(dead_code)]

// UNSOUND: `N` is nonzero, but there is no guard proving `data.len() % N == 0`.
#[rapx::verify]
pub fn unsound_as_chunks_unchecked_missing_exact_div(data: &[u32]) -> usize {
    let chunks = unsafe { data.as_chunks_unchecked::<4>() };
    chunks.len()
}

// UNSOUND: the divisor is nonzero, but the exact-division precondition is missing.
#[rapx::verify]
pub fn unsound_exact_div_missing_guard(data: &[u32]) -> usize {
    unsafe { core::intrinsics::exact_div(data.len(), 4) }
}

#[rapx::verify]
pub fn unsound_generic_exact_div<const N: usize>(data: &[u32]) -> usize {
    unsafe { core::intrinsics::exact_div(data.len(), N) }
}

#[rapx::verify]
pub fn unsound_zst_flat_len<T, const N: usize>(data: &[[T; N]]) -> usize {
    unsafe { data.len().unchecked_mul(N) }
}

#[rapx::verify]
pub fn unsound_flat_len_wrong_count<T, const N: usize>(data: &[[T; N]]) -> usize {
    if core::mem::size_of::<T>() == 0 {
        return 0;
    }
    unsafe { data.len().unchecked_mul(usize::MAX) }
}
