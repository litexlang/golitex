use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::prelude::*;

static NEXT_FIXTURE_ID: AtomicUsize = AtomicUsize::new(0);

struct TrustedPrefixFixture {
    root: PathBuf,
    file: PathBuf,
}

#[test]
fn trust_before_line_trusts_only_statements_before_the_exact_boundary() {
    let fixture = TrustedPrefixFixture::new(
        "exact_boundary",
        r#"1 = 2

2 = 3
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert_eq!(results.len(), 1);
    assert!(
        error.is_some(),
        "the false fact starting at the boundary must fail"
    );
    assert_trace(&results[0], "trusted_prefix", 1, 3);
    let report = runtime
        .trusted_prefix_report
        .as_ref()
        .expect("a valid boundary should produce a report");
    assert_eq!(report.before_line, 3);
    assert_eq!(report.trusted_top_level_statements, 1);
    assert_eq!(report.first_verified_statement_line, 3);
    assert_eq!(runtime.current_execution_mode(), ExecutionMode::Verified);
}

#[test]
fn trust_before_line_rejects_a_non_header_before_execution() {
    let fixture = TrustedPrefixFixture::new(
        "non_header",
        r#"2 = 3

1 = 1
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 2);

    assert!(results.is_empty());
    let message = format!("{:?}", error.expect("a blank-line boundary must fail"));
    assert!(message.contains("must be the header line of a top-level statement"));
    assert!(message.contains("previous top-level statement starts at line 1"));
    assert!(message.contains("next top-level statement starts at line 3"));
    assert!(runtime.trusted_prefix_report.is_none());

    let (probe_results, probe_error) = run_source_code("2 = 3", &mut runtime);
    assert!(
        probe_results.is_empty() && probe_error.is_some(),
        "boundary setup failure must not execute or store the line-1 fact"
    );
    assert_eq!(runtime.current_execution_mode(), ExecutionMode::Verified);
}

#[test]
fn trust_before_line_rejects_a_nested_proof_line_as_the_boundary() {
    let fixture = TrustedPrefixFixture::new(
        "nested_boundary",
        r#"thm enclosing_theorem:
    ? forall:
        1 = 1
    1 = 1

1 = 1
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 2);

    assert!(results.is_empty());
    let message = format!("{:?}", error.expect("a nested proof boundary must fail"));
    assert!(message.contains("must be the header line of a top-level statement"));
    assert!(message.contains("previous top-level statement starts at line 1"));
    assert!(message.contains("next top-level statement starts at line 6"));
    assert!(runtime.trusted_prefix_report.is_none());
}

#[test]
fn trust_before_line_still_rejects_prefix_syntax_errors() {
    let fixture = TrustedPrefixFixture::new(
        "syntax_error",
        r#"thm malformed

1 = 1
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(results.is_empty());
    assert!(error.is_some(), "trusted statements must still parse");
    assert_eq!(runtime.current_execution_mode(), ExecutionMode::Verified);
}

#[test]
fn trust_before_line_still_rejects_duplicate_prefix_declarations() {
    let fixture = TrustedPrefixFixture::new(
        "duplicate",
        r#"have duplicate_object R
have duplicate_object R

1 = 1
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 4);

    assert_eq!(results.len(), 1);
    assert!(
        error.is_some(),
        "trusted declarations must still update the environment"
    );
    assert_trace(&results[0], "trusted_prefix", 1, 4);
    assert_eq!(runtime.current_execution_mode(), ExecutionMode::Verified);
}

#[test]
fn trust_before_line_reports_trusted_and_verified_statement_traces() {
    let fixture = TrustedPrefixFixture::new(
        "trace_status",
        r#"1 = 2

1 = 1
"#,
    );
    let mut runtime = Runtime::new();
    runtime.set_output_style(OutputStyle::Detailed);
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(error.is_none());
    assert_eq!(results.len(), 2);
    assert_trace(&results[0], "trusted_prefix", 1, 3);
    assert_trace(&results[1], "verified", 0, 0);

    let (_, output) = render_run_source_code_output(&runtime, &results, &error, false);
    assert!(output.contains("\"verification_status\": \"trusted_prefix\""));
    assert!(output.contains("\"verification_status\": \"verified\""));
    assert!(output.contains("\"kind\": \"cli_trusted_prefix\""));
    assert!(output.contains("\"kind\": \"trusted_prefix_environment_load\""));
    assert!(!output.contains("\"kind\": \"trusted_environment_load\""));
}

#[test]
fn trust_before_line_does_not_invent_cli_provenance_for_suffix_trust() {
    let fixture = TrustedPrefixFixture::new("suffix_trust", "trust 1 = 2\n");
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 1);

    assert!(error.is_none());
    assert_eq!(results.len(), 1);
    let trace = results[0]
        .execution_trace()
        .expect("the suffix trust statement should have a trace");
    assert_eq!(trace.verification_status.as_deref(), Some("indirect_trust"));
    assert!(trace.trust_summary.contains_kind("trust"));
    assert!(!trace.trust_summary.contains_kind("cli_trusted_prefix"));

    let report = runtime
        .trusted_prefix_report
        .as_ref()
        .expect("the first statement is a valid zero-prefix boundary");
    let summary = display_run_summary_json_with_runtime_and_trusted_prefix(
        &runtime, &results, &error, report,
    );
    assert!(!summary.contains("cli_trusted_prefix"));
}

#[test]
fn trust_before_line_marks_a_suffix_cached_fact_as_indirect_trust() {
    let fixture = TrustedPrefixFixture::new(
        "cached_fact",
        r#"1 = 2

1 = 2
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(error.is_none());
    assert_eq!(results.len(), 2);
    assert_trace(&results[1], "indirect_trust", 1, 3);
}

#[test]
fn trust_before_line_marks_a_suffix_inferred_fact_as_indirect_trust() {
    let fixture = TrustedPrefixFixture::new(
        "inferred_fact",
        r#"2 $in {3}

2 = 3
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(error.is_none());
    assert_eq!(results.len(), 2);
    assert_trace(&results[0], "trusted_prefix", 1, 3);
    assert_trace(&results[1], "indirect_trust", 1, 3);
}

#[test]
fn trust_before_line_marks_a_suffix_theorem_call_as_indirect_trust() {
    let fixture = TrustedPrefixFixture::new(
        "theorem_call",
        r#"thm prefix_false:
    ? forall:
        1 = 2
    1 = 2

thm suffix_from_prefix:
    ? forall:
        1 = 2
    by thm prefix_false()
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 6);

    assert!(
        error.is_none(),
        "suffix theorem should be supplied by the prefix theorem"
    );
    assert_eq!(results.len(), 2);
    assert_trace(&results[0], "trusted_prefix", 1, 6);
    assert_trace(&results[1], "indirect_trust", 1, 6);
    assert!(
        runtime
            .get_thm_trust_summary_by_name("suffix_from_prefix")
            .contains_kind("cli_trusted_prefix"),
        "the suffix theorem interface must retain its indirect CLI trust"
    );
}

#[test]
fn trust_before_line_marks_a_suffix_object_reference_as_indirect_trust() {
    let fixture = TrustedPrefixFixture::new(
        "object_reference",
        r#"have prefix_object R = 1

prefix_object = prefix_object
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(error.is_none());
    assert_eq!(results.len(), 2);
    assert_trace(&results[0], "trusted_prefix", 1, 3);
    assert_trace(&results[1], "indirect_trust", 1, 3);
}

#[test]
fn trust_before_line_propagates_indirect_trust_through_a_suffix_object() {
    let fixture = TrustedPrefixFixture::new(
        "suffix_object_propagation",
        r#"exist x R st {x != x}

obtain y from exist x R st {x != x}

y = y
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(error.is_none());
    assert_eq!(results.len(), 3);
    assert_trace(&results[0], "trusted_prefix", 1, 3);
    assert_trace(&results[1], "indirect_trust", 1, 3);
    assert_trace(&results[2], "indirect_trust", 1, 3);
}

#[test]
fn trust_before_line_top_level_try_commits_its_declarations() {
    let fixture = TrustedPrefixFixture::new(
        "try_commit",
        r#"try:
    have committed_object R = 1
    committed_object = 1

committed_object = 1
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 5);

    assert!(
        error.is_none(),
        "a trusted top-level try must commit its child environment"
    );
    assert_eq!(results.len(), 2);
    assert_trace(&results[0], "trusted_prefix", 1, 5);
    assert_trace(&results[1], "indirect_trust", 1, 5);
}

#[test]
fn trust_before_line_restores_execution_context_after_success_and_error() {
    let successful_fixture = TrustedPrefixFixture::new(
        "restore_success",
        r#"1 = 2

1 = 1
"#,
    );
    let mut successful_runtime = Runtime::new();
    let (_, successful_error) = run_trusted_prefix(&successful_fixture, &mut successful_runtime, 3);
    assert!(successful_error.is_none());
    assert_verified_probe_fails(&mut successful_runtime, "3 = 4");

    let failing_fixture = TrustedPrefixFixture::new(
        "restore_error",
        r#"have repeated_object R
have repeated_object R

1 = 1
"#,
    );
    let mut failing_runtime = Runtime::new();
    let (_, failing_error) = run_trusted_prefix(&failing_fixture, &mut failing_runtime, 4);
    assert!(failing_error.is_some());
    assert_verified_probe_fails(&mut failing_runtime, "4 = 5");
}

impl TrustedPrefixFixture {
    fn new(label: &str, source: &str) -> Self {
        let fixture_id = NEXT_FIXTURE_ID.fetch_add(1, Ordering::Relaxed);
        let root = std::env::temp_dir().join(format!(
            "litex-trust-before-line-{}-{}-{}",
            std::process::id(),
            label,
            fixture_id
        ));
        fs::create_dir_all(&root).expect("create trusted-prefix fixture directory");
        let file = root.join("main.lit");
        fs::write(&file, source).expect("write trusted-prefix fixture source");
        TrustedPrefixFixture { root, file }
    }
}

impl Drop for TrustedPrefixFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn run_trusted_prefix(
    fixture: &TrustedPrefixFixture,
    runtime: &mut Runtime,
    before_line: usize,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    run_file_with_project_context_and_trusted_prefix(
        fixture
            .file
            .to_str()
            .expect("fixture path should be valid UTF-8"),
        runtime,
        true,
        Some(before_line),
    )
}

fn assert_trace(result: &StmtResult, status: &str, statement_line: usize, boundary: usize) {
    let trace = result
        .execution_trace()
        .expect("statement result should have an execution trace");
    assert_eq!(trace.verification_status.as_deref(), Some(status));
    if statement_line == 0 {
        assert!(trace.trust_summary.is_empty());
        return;
    }
    let dependency = trace
        .trust_summary
        .dependencies
        .iter()
        .find(|dependency| dependency.kind == "cli_trusted_prefix")
        .expect("trace should contain CLI trusted-prefix provenance");
    assert_eq!(dependency.line_file.0, statement_line);
    assert_eq!(dependency.boundary, Some(boundary));
}

fn assert_verified_probe_fails(runtime: &mut Runtime, source: &str) {
    assert_eq!(runtime.current_execution_mode(), ExecutionMode::Verified);
    let (results, error) = run_source_code(source, runtime);
    assert!(
        results.is_empty() && error.is_some(),
        "a false probe must be verified after trusted-prefix execution"
    );
    assert_eq!(runtime.current_execution_mode(), ExecutionMode::Verified);
}
