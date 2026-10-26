#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

#[rapx::requires(ValidNum(value <= limit))]
unsafe fn require_bound(value: usize, limit: usize) {}

pub struct Capacity {
    cap: usize,
}

impl Capacity {
    fn len(&self) -> usize {
        self.cap
    }

    fn capacity_ext(&self, size: usize) -> usize {
        if size == 0 { usize::MAX } else { self.cap }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(value <= self.len()))]
    pub unsafe fn sound_len(&self, value: usize) {
        unsafe { require_bound(value, self.cap) }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(value <= self.capacity_ext(size)))]
    pub unsafe fn sound_nonzero(&self, value: usize, size: usize) {
        if size != 0 {
            unsafe { require_bound(value, self.cap) }
        }
    }

    #[rapx::verify]
    #[rapx::requires(ValidNum(value <= self.capacity_ext(size)))]
    pub unsafe fn unsound_zero(&self, value: usize, size: usize) {
        if size == 0 {
            unsafe { require_bound(value, self.cap) }
        }
    }
}
