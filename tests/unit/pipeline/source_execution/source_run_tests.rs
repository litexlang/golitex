use super::SourceRunOutcome;
use crate::module_system::{ModuleId, SourceId, VirtualSource};
use crate::pipeline::run_code;
use crate::result::{
    StmtResult, SuccessProofBlockStmtResult, SuccessStmtResult, TryStmtExecutionResult,
};
use crate::runtime::{RunOptions, Runtime};

fn runtime_with_source_context(name: &str) -> Runtime {
    let mut runtime = Runtime::default();
    runtime.start_virtual_source(VirtualSource::CodeExtraction);
    runtime.set_current_user_lit_file_path(name);
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
    assert!(runtime.current_parse_context().is_at_root_scope());
}

#[test]
fn nested_proof_parse_bindings_are_runtime_owned_and_unwind_after_execution() {
    let mut runtime = runtime_with_source_context("runtime-owned-parse-context.lit");

    let outcome = runtime.execute_source(
        "claim:\n    ? 1 = 1\n    have local_value R = 1\n    local_value = local_value",
    );

    assert!(
        outcome.runtime_error.is_none(),
        "{:?}",
        outcome.runtime_error
    );
    assert_eq!(outcome.stmt_results.len(), 1);
    assert!(runtime.current_parse_context().is_at_root_scope());
}

#[test]
fn failed_nested_parse_restores_the_runtime_owned_parse_context() {
    let mut runtime = runtime_with_source_context("runtime-owned-parse-rollback.lit");

    let outcome = runtime.execute_source(
        "claim:\n    ? 1 = 1\n    have local_value R = 1\n    have local_value R = 2",
    );

    assert!(outcome.runtime_error.is_some());
    assert!(runtime.current_parse_context().is_at_root_scope());
}

#[test]
fn structured_source_run_requires_an_active_source_context() {
    let mut runtime = Runtime::default();

    let outcome = runtime.execute_source("1 = 1");

    assert!(outcome.stmt_results.is_empty());
    assert!(outcome.runtime_error.is_some());
}

#[test]
fn structured_source_run_retains_rolled_back_try_as_a_successful_statement() {
    let mut runtime = runtime_with_source_context("structured-source-try.lit");

    let outcome = runtime.execute_source("try:\n    1 = 0\n");

    assert!(
        outcome.runtime_error.is_none(),
        "{:?}",
        outcome.runtime_error
    );
    let [StmtResult::Success(SuccessStmtResult::ProofBlock(SuccessProofBlockStmtResult::TryStmt(
        result,
    )))] = outcome.stmt_results.as_slice()
    else {
        panic!("expected one successful try statement result")
    };
    assert!(matches!(
        result.execution,
        TryStmtExecutionResult::RolledBack(_)
    ));
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

    assert_eq!(outcome.runtime.current_module_id, Some(ModuleId::ROOT));
    assert_eq!(outcome.runtime.current_source_id, Some(SourceId(0)));
    assert_eq!(outcome.runtime.current_file_path_rc().as_ref(), "eval");
}
