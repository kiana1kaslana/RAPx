//! Compile with rustc -O tools/opt/bench_string_accumulator.rs -o target/opt-review/string-bench
//! Prints raw microsecond samples. Run without concurrent builds.
use std::{hint::black_box, time::Instant};
#[inline(never)]
fn cloned(n: usize, part: &str) -> String {
    let mut s = String::new();
    for _ in 0..n {
        s = s.clone() + black_box(part);
    }
    s
}
#[inline(never)]
fn moved(n: usize, part: &str) -> String {
    let mut s = String::new();
    for _ in 0..n {
        s = s + black_box(part);
    }
    s
}
#[inline(never)]
fn pushed(n: usize, part: &str) -> String {
    let mut s = String::new();
    for _ in 0..n {
        s.push_str(black_box(part));
    }
    s
}
fn main() {
    let variants: [(&str, fn(usize, &str) -> String); 3] = [
        ("clone_add", cloned),
        ("move_add", moved),
        ("push_str", pushed),
    ];
    println!("n,variant,sample,microseconds");
    for n in [100, 1_000, 10_000] {
        let part = black_box("abcdefghijklmnopqrstuvwxyz012345");
        let expected = part.repeat(n);
        for (_, run) in variants {
            assert_eq!(run(n, part), expected);
            for _ in 0..3 {
                black_box(run(n, part));
            }
        }
        for sample in 0..30 {
            // Rotate variant order to reduce systematic order bias.
            for offset in 0..3 {
                let (name, run) = variants[(sample + offset) % variants.len()];
                let start = Instant::now();
                let result = black_box(run(black_box(n), black_box(part)));
                let us = start.elapsed().as_secs_f64() * 1e6;
                assert_eq!(result, expected);
                println!("{n},{name},{sample},{us:.3}");
            }
        }
    }
}
