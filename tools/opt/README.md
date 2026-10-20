# Opt performance experiment

This is a synthetic microbenchmark, not an AI-generated-code dataset or an
end-to-end application speedup claim. It compares explicitly cloning a growing
String with moving it into Add and with push_str. Add already reuses its buffer.

From the repository root in Linux/WSL:

~~~sh
mkdir -p target/opt-review
rustc -O tools/opt/bench_string_accumulator.rs -o target/opt-review/string-bench
taskset -c 0 target/opt-review/string-bench > target/opt-review/string-benchmark.csv
cargo test --manifest-path rapx/tests/opt/string_accumulator/Cargo.toml
cargo test -p rapx --test tests opt_ -- --test-threads=1
~~~

Choose an allowed CPU if CPU 0 is unavailable. Run the benchmark without concurrent
builds. It uses a 32-byte fragment, 3 warmups and 30 measured samples per size,
rotates variant order and checks output equality after each sample. Timing includes
construction, but the final result is dropped after the timed section. No allocation
counter is installed. Small sub-microsecond measurements are noisy.

The committed CSV records one local run on WSL2 / Ryzen 9 7940HX with
rustc 1.101.0-nightly (d080e7dff 2026-09-27), compiled with -O.
It is descriptive data, not a confidence-interval or significance analysis.

See [the opt pipeline study](../../docs/opt-pipeline.zh-CN.md) for semantic
preconditions, remaining limitations, Clippy overlap and the research roadmap.
