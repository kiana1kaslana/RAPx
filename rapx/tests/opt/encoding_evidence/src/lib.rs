#![allow(dead_code)]
pub fn unicode_lowercase() -> String {
    "ÉCOLE".to_lowercase()
}
pub fn unknown_lowercase(s: &str) -> String {
    s.to_lowercase()
}
pub fn invalid_vec() -> Result<String, std::string::FromUtf8Error> {
    let mut v = Vec::new();
    v.push(0xff);
    String::from_utf8(v)
}
pub fn mutated_vec() -> Result<String, std::string::FromUtf8Error> {
    let mut v = Vec::new();
    v.push(b'A');
    v[0] = 0xff;
    String::from_utf8(v)
}
pub fn invalid_array() -> bool {
    let mut a = [0u8; 4];
    a[0] = 0xff;
    std::str::from_utf8(&a).is_ok()
}
pub fn unknown_write(byte: u8) -> bool {
    let mut a = [0u8; 4];
    a[0] = b'A';
    a[1] = byte;
    std::str::from_utf8(&a).is_ok()
}
pub fn lossy_invalid() -> String {
    let mut v = Vec::new();
    v.push(0xff);
    String::from_utf8_lossy(&v).into_owned()
}

pub fn partial_utf8() -> bool {
    let bytes = b"\xc3\xa9";
    std::str::from_utf8(&bytes[1..]).is_ok()
}
pub fn branch_reassignment(flag: bool) -> String {
    let mut text = "ASCII";
    if flag {
        text = "ÉCOLE";
    }
    text.to_lowercase()
}
pub fn unknown_mutation(change: fn(&mut [u8])) -> bool {
    let mut a = [b'A'; 4];
    change(&mut a);
    std::str::from_utf8(&a).is_ok()
}
pub fn same_local(flag: bool) -> (String, String) {
    let mut text = "ÉCOLE";
    let first = text.to_lowercase();
    if flag {
        text = "ASCII";
    }
    (first, text.to_lowercase())
}
pub fn lossy_raw(bytes: &[u8]) -> String {
    String::from_utf8_lossy(bytes).into_owned()
}
