#![allow(dead_code)]
#![allow(unused_variables)]

#![feature(register_tool)]
#![register_tool(rapx)]

// Quadratic accumulation: every `+` reallocates the whole String buffer.
pub fn join(words: &[&str]) -> String {
    let mut out = String::new();
    for w in words {
        out = out + w;
    }
    out
}
