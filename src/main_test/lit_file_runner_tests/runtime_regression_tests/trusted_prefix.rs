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
    assert_trace(&results[0], "trusted_prefix");
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
    assert_trace(&results[0], "trusted_prefix");
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
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");

    let (_, output) = render_run_source_code_output(&runtime, &results, &error, false);
    assert!(output.contains("\"verification_status\": \"trusted_prefix\""));
    assert!(output.contains("\"verification_status\": \"verified\""));
    assert!(!output.contains("\"trust_dependencies\""));
    assert!(output.contains("\"kind\": \"trusted_prefix_environment_load\""));
    assert!(!output.contains("\"kind\": \"trusted_environment_load\""));
}

#[test]
fn trust_before_line_reports_a_suffix_trust_as_verified_execution() {
    let fixture = TrustedPrefixFixture::new("suffix_trust", "trust 1 = 2\n");
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 1);

    assert!(error.is_none());
    assert_eq!(results.len(), 1);
    assert_trace(&results[0], "verified");

    let report = runtime
        .trusted_prefix_report
        .as_ref()
        .expect("the first statement is a valid zero-prefix boundary");
    let summary = display_run_summary_json_with_runtime_and_trusted_prefix(
        &runtime, &results, &error, report,
    );
    assert!(summary.contains("\"direct_trust\": 1"));
    assert!(!summary.contains("indirect_trust"));
    assert!(!summary.contains("trust_dependencies"));
}

#[test]
fn trust_before_line_reuses_a_suffix_cached_fact_without_provenance() {
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
    assert_trace(&results[1], "verified");
}

#[test]
fn trust_before_line_reuses_a_suffix_inferred_fact_without_provenance() {
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
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");
}

#[test]
fn trust_before_line_reuses_a_suffix_theorem_without_provenance() {
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
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");
    assert!(runtime
        .get_thm_definition_by_name("suffix_from_prefix")
        .is_some());
}

#[test]
fn trust_before_line_reuses_a_suffix_object_without_provenance() {
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
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");
}

#[test]
fn trust_before_line_replays_a_let_definition_for_the_verified_suffix() {
    let fixture = TrustedPrefixFixture::new(
        "let_object_reference",
        r#"let prefix_object = 1

prefix_object = 1
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(
        error.is_none(),
        "a trusted let definition should supply its name and equality to the suffix"
    );
    assert_eq!(results.len(), 2);
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");
}

#[test]
fn trust_before_line_reuses_a_suffix_object_fact_without_provenance() {
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
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");
    assert_trace(&results[2], "verified");
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
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");
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

#[test]
fn trust_before_line_replays_builtin_theorem_conclusions_without_rechecking_requirements() {
    let fixture = TrustedPrefixFixture::new(
        "builtin_theorem_replay",
        r#"by thm set_builder_member(0, {x R: x = 1})

0 $in {x R: x = 1}
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(
        error.is_none(),
        "trusted-prefix replay should restore the builtin conclusion: {error:?}"
    );
    assert_eq!(results.len(), 2);
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");
}

#[test]
fn trust_before_line_replays_finite_set_index_existential() {
    let fixture = TrustedPrefixFixture::new(
        "finite_set_index_builtin_theorem_replay",
        r#"by thm finite_set_has_bijective_index({})

obtain idx from exist idx finite_seq({}, finite_set_size({})) st {$bijective(closed_range(1, finite_set_size({})), {}, idx)}
$bijective(closed_range(1, finite_set_size({})), {}, idx)
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(
        error.is_none(),
        "trusted-prefix replay should restore the finite-set index existential: {error:?}"
    );
    assert_eq!(results.len(), 3);
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");
    assert_trace(&results[2], "verified");
}

#[test]
fn trust_before_line_replays_only_the_selected_builtin_theorem_fact() {
    let fixture = TrustedPrefixFixture::new(
        "selected_builtin_theorem_replay",
        r#"by thm set_builder_member(0, {x R: x = 1}) => 0 $in {x R: x = 1}

0 $in {x R: x = 1}
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(
        error.is_none(),
        "trusted-prefix replay should restore only the selected fact: {error:?}"
    );
    assert_eq!(results.len(), 2);
    assert_trace(&results[0], "trusted_prefix");
    assert_trace(&results[1], "verified");
}

#[test]
fn trust_before_line_still_checks_builtin_theorem_arity() {
    let fixture = TrustedPrefixFixture::new(
        "builtin_theorem_bad_arity",
        r#"by thm set_builder_member(0)

1 = 1
"#,
    );
    let mut runtime = Runtime::new();
    let (results, error) = run_trusted_prefix(&fixture, &mut runtime, 3);

    assert!(results.is_empty());
    let message = format!("{:?}", error.expect("wrong arity must fail during replay"));
    assert!(message.contains("expects 2 argument(s), but got 1"));
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

fn assert_trace(result: &StmtResult, status: &str) {
    let trace = result
        .execution_trace()
        .expect("statement result should have an execution trace");
    assert_eq!(trace.verification_status.as_deref(), Some(status));
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
