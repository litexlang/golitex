use crate::execute::exec_stmt_result::{ExecDefinitionStmtResult, ExecStmtResult};
use crate::execute::execute_def_algo_by_cases_stmt::{
    ExecDefAlgoByCasesStmtFailed, ExecDefAlgoByCasesStmtResult,
};
use crate::execute::execute_have_fn_equal_case_by_case_stmt::ExecHaveFnEqualCaseByCaseStmtFailed;
use crate::launch_command::{LaunchCommand, OutputLanguage};
use crate::runtime::Runtime;
use crate::tokenize::Tokenizer;

fn runtime_with_file_env() -> Runtime {
    Runtime::new(LaunchCommand::Eval {
        code: String::new(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
}

fn exec_one(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
    let tokens = Tokenizer::new()
        .tokenize(code, runtime.current_file.clone())
        .expect("tokenize");
    let stmts = runtime.parse(&tokens).expect("parse");
    assert_eq!(stmts.len(), 1, "expected exactly one stmt in:\n{code}");
    runtime
        .exec_stmt(&stmts[0])
        .expect("exec_stmt RuntimeResult")
}

#[test]
fn def_algo_by_cases_succeeds_and_stores() {
    let mut runtime = runtime_with_file_env();
    let algo = "algo nonzero_flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1";
    let r = exec_one(&mut runtime, algo);
    match &r {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAlgoByCases(
            ExecDefAlgoByCasesStmtResult::Success(_),
        )) => {}
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAlgoByCases(
            ExecDefAlgoByCasesStmtResult::Failed(f),
        )) => panic!("algo failed: {f:?}"),
        other => panic!("unexpected result: failed={}", other.is_failed()),
    }
    assert!(
        runtime.def_algo_visible_in_stack("nonzero_flag").is_some(),
        "algo should be stored"
    );
}

#[test]
fn def_algo_by_cases_incomplete_coverage_soft_fails() {
    let mut runtime = runtime_with_file_env();
    let r = exec_one(&mut runtime, "algo g(x R) R by cases:\n    case x = 0: 0");
    match r {
        ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAlgoByCases(
            ExecDefAlgoByCasesStmtResult::Failed(ExecDefAlgoByCasesStmtFailed::DefineFn(
                ExecHaveFnEqualCaseByCaseStmtFailed::Coverage(_),
            )),
        )) => {}
        other => panic!(
            "expected coverage DefineFn fail, got failed={}",
            other.is_failed()
        ),
    }
}

#[test]
fn def_algo_by_cases_via_run_eval_like_cli() {
    use crate::run::run_eval::run_eval;
    let code = "algo nonzero_flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1\n\neval nonzero_flag(0)";
    let result = run_eval(LaunchCommand::Eval {
        code: code.to_string(),
        session: false,
        strict: false,
        language: OutputLanguage::English,
    })
    .expect("run_eval");
    assert!(
        result.run.success,
        "cli-like run_eval should succeed; failed_indices={:?} session={:?}",
        result.run.failed_statement_results,
        result.run.session_error.is_some()
    );
    assert_eq!(result.run.statement_results.len(), 2);
    assert!(!result.run.statement_results[1].is_failed());
}
