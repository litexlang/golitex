use super::{
    execute_source_with_options, SourceRunFailureKind, SourceRunOptions, SourceRunOutcome,
};
use crate::runtime::Runtime;

fn runtime_with_source_context(name: &str) -> Runtime {
    let mut runtime = Runtime::new();
    runtime.start_isolated_source(name);
    runtime
}

#[test]
fn structured_source_run_reports_success() {
    let mut runtime = runtime_with_source_context("structured-source-success.lit");

    let SourceRunOutcome {
        stmt_results,
        runtime_error,
        failure_kind,
    } = execute_source_with_options("1 = 1", &mut runtime, SourceRunOptions::default());

    assert_eq!(stmt_results.len(), 1);
    assert!(runtime_error.is_none(), "{runtime_error:?}");
    assert!(failure_kind.is_none());
}

#[test]
fn structured_source_run_requires_an_active_source_context() {
    let mut runtime = Runtime::new();

    let outcome = execute_source_with_options("1 = 1", &mut runtime, SourceRunOptions::default());

    assert!(outcome.stmt_results.is_empty());
    assert!(outcome.runtime_error.is_some());
    assert_eq!(outcome.failure_kind, Some(SourceRunFailureKind::Other));
}

#[test]
fn structured_source_run_preserves_try_failure_classification() {
    let mut runtime = runtime_with_source_context("structured-source-try.lit");

    let outcome = execute_source_with_options(
        "try:\n    clear\n",
        &mut runtime,
        SourceRunOptions::default(),
    );

    assert!(outcome.runtime_error.is_some());
    assert_eq!(outcome.failure_kind, Some(SourceRunFailureKind::TryStmt));
}

#[test]
fn trusted_prefix_boundary_must_name_a_top_level_statement_line() {
    let mut runtime = runtime_with_source_context("structured-source-prefix.lit");

    let outcome = execute_source_with_options(
        "1 = 1\n\n2 = 2\n",
        &mut runtime,
        SourceRunOptions {
            trust_before_line: Some(2),
            ..SourceRunOptions::default()
        },
    );

    assert!(outcome.stmt_results.is_empty());
    assert!(outcome.runtime_error.is_some());
    assert_eq!(outcome.failure_kind, Some(SourceRunFailureKind::Other));
}
