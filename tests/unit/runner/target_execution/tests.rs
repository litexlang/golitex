use super::*;

const LARGE_TEST_STACK_SIZE: usize = 64 * 1024 * 1024;

fn run_runner_for_code(code: &str, label: &str, hide_file_paths: bool) -> (bool, String) {
    run_runner_for_code_with_language(code, label, hide_file_paths, OutputLanguage::English)
}

fn run_runner_for_code_with_language(
    code: &str,
    label: &str,
    hide_file_paths: bool,
    output_language: OutputLanguage,
) -> (bool, String) {
    run_runner_on_source("code", label, code, hide_file_paths, false, output_language)
}

fn run_with_large_stack(test_name: &str, f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .name(test_name.to_string())
        .stack_size(LARGE_TEST_STACK_SIZE)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn runner_success_returns_trace() {
    let (ok, output) = run_runner_for_code("1 + 1 = 2", "-runner-test", true);

    assert!(ok, "runner success run failed:\n{}", output);
    assert!(output.contains("\"runner\": \"litex-runner\""));
    assert!(output.contains("\"result\": \"success\""));
    assert!(output.contains("\"trace\""));
}

#[test]
fn runner_failure_returns_trace() {
    let (ok, output) = run_runner_for_code("1 = 0", "-runner-test", true);

    assert!(!ok, "runner unknown run should fail:\n{}", output);
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains("\\\"error_type\\\": \\\"VerifyError\\\""));
    assert!(output.contains("\\\"error_type\\\": \\\"UnknownError\\\""));
    assert!(output.contains("\\\"phases\\\": {"));
    assert!(output.contains("\\\"failed_goal\\\": \\\"1 = 0\\\""));
    assert!(output.contains("\\\"unknown_result\\\": {"));
}

#[test]
fn runner_target_error_returns_message() {
    let (ok, output) = run_runner_for_file("does_not_exist.lit", true);

    assert!(!ok, "runner target error should fail:\n{}", output);
    assert!(output.contains("\"target\": {\n    \"kind\": \"file\",\n    \"label\": \"entry\""));
    assert!(output.contains("\"error\": null"));
    assert!(output.contains("\\\"error_type\\\": \\\"ParseError\\\""));
    assert!(output.contains("\\\"source_kind\\\": \\\"file\\\""));
    assert!(output.contains("does_not_exist.lit"));
    assert!(!output.contains("\"kind\": \"target_error\""));
}

#[test]
fn runner_accepts_trust_as_normal_execution() {
    let (ok, output) = run_runner_for_code("trust 1 = 0", "-runner-test", true);

    assert!(ok, "runner should not reject trust statements:\n{}", output);
    assert!(output.contains("\"result\": \"success\""));
}

#[test]
fn runner_accepts_trust_have_as_normal_execution() {
    run_with_large_stack("runner_accepts_trust_have_as_normal_execution", || {
        let (ok, output) = run_runner_for_code("trust have x R", "-runner-test", true);

        assert!(
            ok,
            "runner should not reject trust have statements:\n{}",
            output
        );
        assert!(output.contains("\"result\": \"success\""));
    });
}

#[test]
fn zh_runner_keeps_machine_wrapper_keys_and_localizes_trace() {
    let (ok, output) = run_runner_for_code_with_language(
        "trust 1 = 1",
        "-runner-test",
        true,
        OutputLanguage::SimplifiedChinese,
    );

    assert!(ok, "Chinese runner should succeed:\n{}", output);
    assert!(output.contains("\"runner\": \"litex-runner\""));
    assert!(output.contains("\"result\": \"success\""));
    assert!(output.contains("\"trace\""));
    assert!(output.contains("\\\"kind\\\": \\\"TrustStmt\\\""));
}

#[test]
fn non_english_runner_keeps_machine_wrapper_keys() {
    for language in [
        OutputLanguage::SimplifiedChinese,
        OutputLanguage::TraditionalChinese,
        OutputLanguage::Japanese,
        OutputLanguage::Korean,
        OutputLanguage::Spanish,
        OutputLanguage::French,
        OutputLanguage::German,
        OutputLanguage::Portuguese,
        OutputLanguage::Russian,
        OutputLanguage::Arabic,
        OutputLanguage::Hindi,
        OutputLanguage::Vietnamese,
        OutputLanguage::Indonesian,
    ] {
        let (ok, output) =
            run_runner_for_code_with_language("trust 1 = 1", "-runner-test", true, language);

        assert!(ok, "localized runner should succeed:\n{}", output);
        assert!(output.contains("\"runner\": \"litex-runner\""));
        assert!(output.contains("\"result\": \"success\""));
        assert!(output.contains("\"ok\": true"));
        assert!(output.contains("\"target\""));
        assert!(output.contains("\"trace\""));
    }
}

#[test]
fn strict_runner_rejects_user_trust() {
    let (ok, output) = run_runner_for_code_strict("trust 1 = 0", "-runner-test", true);

    assert!(
        !ok,
        "strict runner should reject trust statements:\n{}",
        output
    );
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains(TrustStmt::strict_mode_rejection_message()));
}

#[test]
fn strict_runner_rejects_user_axiom() {
    let source_code = r#"
axiom strict_axiom:
    ? forall:
        1 = 1
"#;
    let (ok, output) = run_runner_for_code_strict(source_code, "-runner-test", true);

    assert!(
        !ok,
        "strict runner should reject axiom statements:\n{}",
        output
    );
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains(AxiomStmt::strict_mode_rejection_message()));
}

#[test]
fn strict_runner_rejects_user_trust_have() {
    run_with_large_stack("strict_runner_rejects_user_trust_have", || {
        let (ok, output) = run_runner_for_code_strict("trust have x R", "-runner-test", true);

        assert!(
            !ok,
            "strict runner should reject trust have statements:\n{}",
            output
        );
        assert!(output.contains("\"result\": \"error\""));
        assert!(output.contains(TrustHaveStmt::strict_mode_rejection_message()));
    });
}
