#![allow(dead_code)]
pub fn disjunction(a: &[u8], i: usize, force: bool) -> u8 {
    if i < a.len() || force { a[i] } else { 0 }
}
pub fn negation(a: &[u8], i: usize) -> u8 {
    if !(i < a.len()) { a[i] } else { 0 }
}
pub fn unrelated(a: &[u8], b: &[u8], i: usize) -> u8 {
    if i < a.len() { b[i] } else { 0 }
}
