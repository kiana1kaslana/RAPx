#![allow(dead_code)]
pub fn ascii_literal() -> String {
    "HELLO".to_lowercase()
}
pub fn ascii_alias() -> String {
    let a = "HELLO";
    let b = a;
    b.to_lowercase()
}
pub fn utf8_roundtrip(s: &str) -> &str {
    let bytes = s.as_bytes();
    let alias = bytes;
    std::str::from_utf8(alias).unwrap()
}
pub fn valid_multibyte() -> &'static str {
    std::str::from_utf8(b"\xc3\xa9").unwrap()
}
pub fn ascii_array() -> bool {
    let a = [b'A'; 4];
    std::str::from_utf8(&a).is_ok()
}
pub fn utf8_array() -> bool {
    let a = [0xc3u8, 0xa9];
    std::str::from_utf8(&a).is_ok()
}
pub fn owned_roundtrip(s: &str) -> String {
    let bytes = s.as_bytes().to_vec();
    String::from_utf8(bytes).unwrap()
}
pub fn independent_candidates(s: &str) -> (String, String) {
    // An unknown candidate must not clear an independently proven finding.
    (s.to_lowercase(), "ASCII".to_lowercase())
}
