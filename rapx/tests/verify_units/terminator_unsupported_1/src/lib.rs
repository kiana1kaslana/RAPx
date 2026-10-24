#![feature(register_tool, explicit_tail_calls, coroutines, coroutine_trait)]
#![register_tool(rapx)]
#![allow(dead_code, incomplete_features, unused_variables)]

#[rapx::requires(ValidNum(value != 0))]
unsafe fn need_nonzero(value: u32) {}

#[rapx::verify]
pub unsafe fn unsound_tail_call(value: u32) {
    unsafe { become need_nonzero(0) }
}

#[rapx::verify]
pub unsafe fn sound_tail_call(value: u32) {
    unsafe { become need_nonzero(1) }
}

#[rapx::verify]
pub unsafe fn unsound_tail_call_input(value: u32) {
    unsafe { become need_nonzero(value) }
}

#[rapx::verify]
pub unsafe fn sound_tail_call_guarded(value: u32) {
    let selected = if value == 0 { 1 } else { value };
    unsafe { become need_nonzero(selected) }
}

fn identity(value: u32) -> u32 {
    value
}

fn tail_identity(value: u32) -> u32 {
    become identity(value)
}

#[rapx::verify]
pub fn unsound_after_tail_helper() {
    let result = tail_identity(0);
    unsafe { need_nonzero(result) };
}

#[rapx::verify]
pub fn sound_after_tail_helper() {
    let result = tail_identity(1);
    unsafe { need_nonzero(result) };
}

fn write_zero(value: &mut u32) {
    *value = 0;
}

fn tail_write(value: &mut u32) {
    become write_zero(value)
}

#[rapx::verify]
pub fn unsound_after_tail_write() {
    let mut value = 1;
    tail_write(&mut value);
    unsafe { need_nonzero(value) };
}

#[rapx::verify]
pub unsafe fn unknown_tail_fnptr(value: u32) {
    let function: unsafe fn(u32) = need_nonzero;
    unsafe { become function(0) }
}

#[rapx::verify]
pub fn unknown_indirect_call(function: unsafe fn(u32)) {
    unsafe { function(0) };
}

pub fn make_coroutine() -> impl std::ops::Coroutine<Yield = (), Return = ()> {
    #[coroutine]
    || {
        yield ();
        unsafe { need_nonzero(0) };
    }
}
