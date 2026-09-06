use super::*;

const LARGE_TEST_STACK_SIZE: usize = 64 * 1024 * 1024;

fn run_runner_for_test(code: &str, options: LitexExecutionOptions) -> (bool, String) {
    render_runner(run_eval_command(code, options), true)
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
    let (ok, output) = run_runner_for_test("1 + 1 = 2", LitexExecutionOptions::default());

    assert!(ok, "runner success run failed:\n{}", output);
    assert!(output.contains("\"runner\": \"litex-runner\""));
    assert!(output.contains("\"runner_version\": \"0.2\""));
    assert!(output.contains("\"result\": \"success\""));
    assert!(output.contains("\"target\": {\n    \"kind\": \"code\"\n  }"));
    assert!(!output.contains("\"label\""));
    assert!(!output.contains("\"path\""));
    assert!(output.contains("\"trace\""));
    assert!(!output.contains("\"pipeline_trace\""));
}

#[test]
fn runner_failure_returns_trace() {
    let (ok, output) = run_runner_for_test("1 = 0", LitexExecutionOptions::default());

    assert!(!ok, "runner unknown run should fail:\n{}", output);
    assert!(output.contains("\"result\": \"error\""));
    assert!(output.contains("\\\"kind\\\": \\\"verify_error\\\""));
    assert!(output.contains("\\\"kind\\\": \\\"unknown_error\\\""));
    assert!(!output.contains("\\\"phases\\\":"));
    assert!(output.contains("\\\"failed_goal\\\": \\\"1 = 0\\\""));
    assert!(output.contains("\\\"unknown_result\\\": {"));
}

#[test]
fn runner_target_error_returns_message() {
    let (ok, output) = render_runner(
        run_file_command("does_not_exist.lit", LitexExecutionOptions::default()),
        true,
    );

    assert!(!ok, "runner target error should fail:\n{}", output);
    assert!(output.contains("\"target\": {\n    \"kind\": \"file\"\n  }"));
    assert!(!output.contains("\"label\""));
    assert!(output.contains("\"error\": null"));
    assert!(output.contains("\\\"kind\\\": \\\"parse_error\\\""));
    assert!(output.contains("\\\"source_kind\\\": \\\"file\\\""));
    assert!(output.contains("does_not_exist.lit"));
    assert!(!output.contains("\"kind\": \"target_error\""));
}

#[test]
fn detailed_runner_exposes_a_real_target_path_without_a_label() {
    let outcome = run_file_command("does_not_exist.lit", LitexExecutionOptions::default());
    let expected_path = outcome
        .target
        .path()
        .map(str::to_string)
        .expect("file outcome should retain its resolved path");
    let (_, output) = render_runner(outcome, false);

    assert!(output.contains("\"kind\": \"file\""));
    assert!(output.contains("\"path\":"));
    assert!(output.contains(expected_path.as_str()));
    assert!(!output.contains("\"label\""));
}

#[test]
fn runner_accepts_trust_as_normal_execution() {
    let (ok, output) = run_runner_for_test("trust 1 = 0", LitexExecutionOptions::default());

    assert!(ok, "runner should not reject trust statements:\n{}", output);
    assert!(output.contains("\"result\": \"success\""));
}

#[test]
fn runner_accepts_trust_have_as_normal_execution() {
    run_with_large_stack("runner_accepts_trust_have_as_normal_execution", || {
        let (ok, output) = run_runner_for_test("trust have x R", LitexExecutionOptions::default());

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
    let (ok, output) = run_runner_for_test(
        "trust 1 = 1",
        LitexExecutionOptions::new(
            VerifyStrictnessPolicy::Ordinary,
            OutputDetail::Normal,
            OutputLanguage::SimplifiedChinese,
            SummaryOption::None,
        ),
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
        let (ok, output) = run_runner_for_test(
            "trust 1 = 1",
            LitexExecutionOptions::new(
                VerifyStrictnessPolicy::Ordinary,
                OutputDetail::Normal,
                language,
                SummaryOption::None,
            ),
        );

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
    let (ok, output) = run_runner_for_test(
        "trust 1 = 0",
        LitexExecutionOptions::strict(
            OutputDetail::Normal,
            OutputLanguage::English,
            SummaryOption::None,
        ),
    );

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
    let (ok, output) = run_runner_for_test(
        source_code,
        LitexExecutionOptions::strict(
            OutputDetail::Normal,
            OutputLanguage::English,
            SummaryOption::None,
        ),
    );

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
        let (ok, output) = run_runner_for_test(
            "trust have x R",
            LitexExecutionOptions::strict(
                OutputDetail::Normal,
                OutputLanguage::English,
                SummaryOption::None,
            ),
        );

        assert!(
            !ok,
            "strict runner should reject trust have statements:\n{}",
            output
        );
        assert!(output.contains("\"result\": \"error\""));
        assert!(output.contains(TrustHaveStmt::strict_mode_rejection_message()));
    });
}
