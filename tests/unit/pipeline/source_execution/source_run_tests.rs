use super::{SourceRunFailureKind, SourceRunOutcome};
use crate::module_system::{FileId, ModuleId};
use crate::pipeline::run_code;
use crate::runtime::{RunOptions, Runtime};

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
    } = runtime.execute_source("1 = 1");

    assert_eq!(stmt_results.len(), 1);
    assert!(runtime_error.is_none(), "{runtime_error:?}");
}

#[test]
fn structured_source_run_requires_an_active_source_context() {
    let mut runtime = Runtime::default();

    let outcome = runtime.execute_source("1 = 1");

    assert!(outcome.stmt_results.is_empty());
    assert!(outcome.runtime_error.is_some());
}

#[test]
fn structured_source_run_preserves_try_failure_classification() {
    let mut runtime = runtime_with_source_context("structured-source-try.lit");

    let (outcome, failure_kind) = runtime
        .execute_source_classified("try:\n    1 = 0\n")
        .into_parts();

    assert!(outcome.runtime_error.is_some());
    assert_eq!(failure_kind, Some(SourceRunFailureKind::TryStmt));
}

#[test]
fn source_import_is_rejected_even_in_an_isolated_source_context() {
    let mut runtime = runtime_with_source_context("isolated-source-import.lit");

    let outcome = runtime.execute_source("import std basics");

    assert!(outcome.stmt_results.is_empty());
    let error = outcome.runtime_error.expect("source import should fail");
    assert!(
        error
            .trace_message()
            .contains("`import` is a terminal command, not a Litex statement"),
        "{}",
        error.trace_message()
    );
}

#[test]
fn code_run_uses_the_explicit_e_source_label() {
    let outcome = run_code("1 = 1", RunOptions::default());

    let frame = outcome
        .runtime
        .execution_stack
        .last()
        .expect("code run should retain its source frame");
    assert_eq!(frame.module_file_info.module_id, ModuleId::ROOT);
    assert_eq!(frame.module_file_info.file_id, FileId(0));
    assert_eq!(frame.module_file_info.source_path.as_ref(), "<-e>");
}
