use super::*;

fn run_sequence_source(source: &str, label: &str) -> (bool, String) {
    let mut runtime = Runtime::new();
    runtime.new_file_path_new_env_new_name_scope(label);
    let (stmt_results, runtime_error) = run_source_code(source, &mut runtime);
    let (run_succeeded, run_output) =
        render_run_source_code_output(&runtime, &stmt_results, &runtime_error, false);
    (run_succeeded, run_output)
}

#[test]
fn finite_sequence_literals_include_the_empty_sequence() {
    let source = r#"
[] = []
[] $in finite_seq({}, 0)
$is_nonempty_set(finite_seq({}, 0))
[1] $in finite_seq(R, 1)
"#;
    let (succeeded, output) = run_sequence_source(source, "finite_sequence_literal_zero_length");
    assert!(
        succeeded,
        "zero- and positive-length finite sequences should both be valid:\n{output}"
    );
    assert!(output.contains("finite seq set is nonempty when length is zero"));
    assert!(output.contains("finite_seq list: length equals n and each entry in co-domain"));
}

#[test]
fn finite_sequence_length_is_natural_and_literal_length_must_match() {
    for (label, source, expected) in [
        (
            "finite_sequence_negative_length",
            "finite_seq(R, -1) = finite_seq(R, -1)",
            "is not verified in N",
        ),
        (
            "empty_sequence_wrong_length",
            "[] $in finite_seq(R, 1)",
            "verification failed",
        ),
    ] {
        let (succeeded, output) = run_sequence_source(source, label);
        assert!(!succeeded, "{label} must fail:\n{output}");
        assert!(
            output.contains(expected),
            "{label} should explain its boundary:\n{output}"
        );
    }
}

#[test]
fn finite_sequence_function_properties_use_exact_one_based_domain_bridge() {
    for (label, source) in [
        (
            "finite_sequence_one_based_domain",
            "have f finite_seq({1}, 1)\ntrust $bijective(closed_range(1, 1), {1}, f)",
        ),
        (
            "empty_finite_sequence_one_based_domain",
            "have f finite_seq({}, 0)\ntrust $bijective(closed_range(1, 0), {}, f)",
        ),
    ] {
        let (succeeded, output) = run_sequence_source(source, label);
        assert!(
            succeeded,
            "the exact finite-sequence domain bridge should be well-defined:\n{output}"
        );
    }

    for (label, source) in [
        (
            "finite_sequence_domain_wrong_start",
            "have f finite_seq({1}, 1)\ntrust $bijective(closed_range(0, 1), {1}, f)",
        ),
        (
            "finite_sequence_domain_wrong_end",
            "have f finite_seq({1}, 1)\ntrust $bijective(closed_range(1, 2), {1}, f)",
        ),
        (
            "finite_sequence_domain_strict_bound",
            "have f fn(k N+: k < 2) {1}\ntrust $bijective(closed_range(1, 1), {1}, f)",
        ),
        (
            "finite_sequence_domain_wrong_carrier",
            "have f fn(k N: k <= 1) {1}\ntrust $bijective(closed_range(1, 1), {1}, f)",
        ),
        (
            "finite_sequence_domain_extra_condition",
            "have f fn(k N+: k <= 1, k > 0) {1}\ntrust $bijective(closed_range(1, 1), {1}, f)",
        ),
    ] {
        let (succeeded, output) = run_sequence_source(source, label);
        assert!(
            !succeeded,
            "a near-miss domain must not match the finite-sequence bridge:\n{output}"
        );
        assert!(output.contains("requires sets A and B and a function with type fn(x A) B"));
    }
}

#[test]
fn finite_sequence_membership_does_not_imply_bijectivity() {
    let source = r#"
have f finite_seq({1}, 1)
$bijective(closed_range(1, 1), {1}, f)
"#;
    let (succeeded, output) =
        run_sequence_source(source, "finite_sequence_is_not_automatically_bijective");
    assert!(
        !succeeded,
        "an arbitrary finite sequence must not be treated as a bijection:\n{output}"
    );
    assert!(output.contains("verification failed"));
    assert!(!output.contains("builtin theorem `finite_set_has_bijective_index`"));
}
