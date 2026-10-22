#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(_value > 0), kind = "precond")]
unsafe fn require_positive(_value: u8) {}

#[rapx::requires(ValidNum(_value != 255), kind = "precond")]
unsafe fn require_not_max(_value: u8) {}

fn conditional_zero(slot: &mut u8, flag: bool) {
    if flag {
        *slot = 0;
    }
}

fn unconditional_zero(slot: &mut u8) {
    *slot = 0;
}

macro_rules! eight_barriers {
    () => {
        std::hint::black_box(0u8);
        std::hint::black_box(0u8);
        std::hint::black_box(0u8);
        std::hint::black_box(0u8);
        std::hint::black_box(0u8);
        std::hint::black_box(0u8);
        std::hint::black_box(0u8);
        std::hint::black_box(0u8);
    };
}

fn conditional_zero_large(slot: &mut u8, flag: bool) {
    if flag {
        *slot = 0;
    }
    eight_barriers!();
    eight_barriers!();
    eight_barriers!();
    eight_barriers!();
    eight_barriers!();
}

#[rapx::verify]
pub fn conditional_write(flag: bool) {
    let mut value = 1u8;
    conditional_zero(&mut value, flag);
    unsafe { require_positive(value) }
}

#[rapx::verify]
pub fn unconditional_write() {
    let mut value = 1u8;
    unconditional_zero(&mut value);
    unsafe { require_positive(value) }
}

#[rapx::verify]
pub fn conditional_write_noninlined(flag: bool) {
    let mut value = 1u8;
    conditional_zero_large(&mut value, flag);
    unsafe { require_positive(value) }
}

#[rapx::verify]
pub fn saturating_sub_zero() {
    let value = 0u8.saturating_sub(1);
    unsafe { require_positive(value) }
}

#[rapx::verify]
pub fn saturating_add_max() {
    let value = 255u8.saturating_add(1);
    unsafe { require_not_max(value) }
}

#[rapx::verify]
pub fn wrapping_sub_max() {
    let value = 0u8.wrapping_sub(1);
    unsafe { require_not_max(value) }
}
