use super::{SourceImportPolicy, SourceRunFailureKind, SourceRunOutcome};
use crate::runtime::Runtime;

fn runtime_with_source_context(name: &str) -> Runtime {
    let mut runtime = Runtime::default();
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
    } = runtime.execute_source("1 = 1", SourceImportPolicy::UseRuntimePolicy);

    assert_eq!(stmt_results.len(), 1);
    assert!(runtime_error.is_none(), "{runtime_error:?}");
    assert!(failure_kind.is_none());
}

#[test]
fn structured_source_run_requires_an_active_source_context() {
    let mut runtime = Runtime::default();

    let outcome = runtime.execute_source("1 = 1", SourceImportPolicy::UseRuntimePolicy);

    assert!(outcome.stmt_results.is_empty());
    assert!(outcome.runtime_error.is_some());
    assert_eq!(outcome.failure_kind, Some(SourceRunFailureKind::Other));
}

#[test]
fn structured_source_run_preserves_try_failure_classification() {
    let mut runtime = runtime_with_source_context("structured-source-try.lit");

    let outcome = runtime.execute_source("try:\n    1 = 0\n", SourceImportPolicy::UseRuntimePolicy);

    assert!(outcome.runtime_error.is_some());
    assert_eq!(outcome.failure_kind, Some(SourceRunFailureKind::TryStmt));
}
