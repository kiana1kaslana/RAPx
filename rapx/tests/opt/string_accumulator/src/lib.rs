#![allow(dead_code, unused_assignments)]
pub fn cloned(parts: &[&str]) -> String {
    let mut output = String::new();
    for part in parts {
        output = output.clone() + part;
    }
    output
}
pub fn nested(parts: &[&str]) -> String {
    let mut output = String::new();
    for _ in 0..2 {
        for part in parts {
            output = output.clone() + part;
        }
    }
    output
}
pub fn moved(parts: &[&str]) -> String {
    let mut output = String::new();
    for part in parts {
        output = output + part;
    }
    output
}
pub fn inplace(parts: &[&str]) -> String {
    let mut output = String::new();
    for part in parts {
        output += part;
    }
    output
}
pub fn push(parts: &[&str]) -> String {
    let mut output = String::new();
    for part in parts {
        output.push_str(part);
    }
    output
}
pub fn fresh(parts: &[&str]) {
    for part in parts {
        let mut output = String::new();
        output = output.clone() + part;
        std::hint::black_box(output);
    }
}
pub fn once(mut output: String, part: &str) -> String {
    output = output.clone() + part;
    output
}
pub fn different(parts: &[&str], source: &String) -> String {
    let mut output = String::new();
    for part in parts {
        output = source.clone() + part;
    }
    output
}
pub fn numbers() -> u64 {
    let mut x = 1u64;
    for _ in 0..5 {
        x = x.clone() + 1;
    }
    x
}
#[test]
fn outputs_agree() {
    for parts in [
        vec![],
        vec![""],
        vec!["hello", " ", "world"],
        vec!["é", "中文", "🦀"],
    ] {
        let expected = parts.concat();
        assert_eq!(cloned(&parts), expected);
        assert_eq!(moved(&parts), expected);
        assert_eq!(inplace(&parts), expected);
        assert_eq!(push(&parts), expected);
    }
}

pub fn reset(parts: &[&str]) -> String {
    let mut output = String::new();
    for part in parts {
        output.clear();
        output = output.clone() + part;
    }
    output
}
pub fn reassigned(parts: &[&str]) -> String {
    let mut output = String::new();
    for part in parts {
        output = String::new();
        output = output.clone() + part;
    }
    output
}
