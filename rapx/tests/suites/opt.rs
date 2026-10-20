#[test]
fn opt_bounds_len() {
    let output = run_opt_fixture("opt/bounds_len");
    assert_not_contain(&output, "RAPx|ERROR|");
    assert_contain(&output, "Potential optimizations detected");
    // Two Vec indexing sites plus the direct while guard (previously skipped).
    assert_contain(&output, "Bounds Checking: 3");
    assert_not_contain(&output, "Use unsafe APIs");
}

#[test]
fn opt_encoding_check() {
    let output = run_opt_fixture("opt/encoding_check");
    assert_not_contain(&output, "RAPx|ERROR|");
    // Both fixtures mutate buffers. The conservative evidence phase does not
    // yet model their writes, so it must not recommend unchecked conversions.
    assert_not_contain(&output, "Redundant UTF-8 validation candidate");
}

#[test]
fn opt_hash_key_cloning() {
    let output = run_opt_fixture("opt/hash_key_cloning");
    assert_not_contain(&output, "RAPx|ERROR|");
    assert_contain(&output, "Potential optimizations detected");
    assert_contain(&output, "Cloning: 1");
}

/// Unlike a negative substring assertion alone, this also fails on compiler or
/// analyzer crashes. Keep this local to opt rather than changing other suites.
fn run_opt_fixture(dir: &str) -> String {
    let path = project_path(dir);
    let _lock = LockGuard::new(path.join(".rapx-test.lock"));
    let output = cargo_rapx_command()
        .arg("opt")
        .current_dir(path)
        .output()
        .expect("run opt fixture");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    assert!(output.status.success(), "opt failed:\n{stderr}");
    assert_contain(&stderr, "Start analysis with RAPx");
    assert_not_contain(&stderr, "RAPx|ERROR|");
    assert_not_contain(&stderr, "panicked at");
    stderr
}

#[test]
fn opt_encoding_rejects_unproved_inputs() {
    let output = run_opt_fixture("opt/encoding_evidence");
    assert_not_contain(&output, "Redundant UTF-8 validation candidate");
    assert_not_contain(&output, "ASCII lowercase opportunity");
    assert_not_contain(&output, "Use unsafe APIs");
}

#[test]
fn opt_encoding_requires_value_evidence() {
    let output = run_opt_fixture("opt/encoding_proven");
    assert_contain(&output, "Encoding Checking: 8");
    assert_eq!(
        output.matches("ASCII lowercase opportunity").count(),
        3,
        "{output}"
    );
    assert_eq!(
        output
            .matches("Redundant UTF-8 validation candidate")
            .count(),
        5,
        "{output}"
    );
}

#[test]
fn opt_string_accumulator_requires_loop_carried_clone() {
    let output = run_opt_fixture("opt/string_accumulator");
    assert_eq!(
        output
            .matches("Repeated String accumulator cloning")
            .count(),
        2,
        "{output}"
    );
    assert_contain(&output, "Suboptimal: 2");
}

#[test]
fn opt_bounds_requires_a_true_guard() {
    let output = run_opt_fixture("opt/bounds_conditions");
    assert_not_contain(&output, "Bounds-check optimization candidate");
    assert_not_contain(&output, "Use unsafe APIs");
}
