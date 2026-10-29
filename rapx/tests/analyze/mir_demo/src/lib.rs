// Covers every body kind `cargo rapx analyze mir` prints: functions, methods,
// closures, async bodies, constants, statics, anonymous constants and ctors.

pub const LIMIT: usize = 8;
pub static GREETING: &str = "hi";

pub struct Buf {
    data: Vec<u8>,
}

impl Buf {
    pub fn new() -> Self {
        Buf { data: Vec::new() }
    }

    pub fn push(&mut self, b: u8) -> bool {
        if self.data.len() >= LIMIT {
            return false;
        }
        self.data.push(b);
        true
    }

    /// # Safety
    /// `self` must hold at least one byte.
    pub unsafe fn first_unchecked(&self) -> u8 {
        let p = self.data.as_ptr();
        unsafe { *p }
    }
}

pub fn sum(xs: &[u32]) -> u32 {
    let mut s = 0;
    for x in xs {
        s += *x;
    }
    s
}

pub fn apply<F: Fn(u32) -> u32>(f: F, v: u32) -> u32 {
    f(v)
}

pub fn closure_user() -> u32 {
    apply(|x| x + 1, 2)
}

pub fn call_ptr(f: fn(u32) -> u32) -> u32 {
    f(1)
}

pub enum Shape {
    Circle(f64),
    Square(f64),
}

pub fn area(s: &Shape) -> f64 {
    match s {
        Shape::Circle(r) => 3.14 * r * r,
        Shape::Square(a) => a * a,
    }
}

pub async fn add_one(x: u32) -> u32 {
    x + 1
}

pub fn zeros() -> [u8; 4] {
    [0; 4]
}

pub fn dropper(v: Vec<String>) -> usize {
    let n = v.len();
    drop(v);
    n
}
