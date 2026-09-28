//! `algo f(…) R by cases:` — define fn (same strength as `have fn … by cases`) and store algo.
//!
//! Example:
//!   algo nonzero_flag(x R) R by cases:
//!       case x = 0: 0
//!       case x != 0: 1

use crate::new_pipeline::ast::stmt::{DefAlgoByCasesStmt, HaveFnEqualCaseByCaseStmt};
use crate::new_pipeline::exec_env::StoredDefAlgo;
use crate::new_pipeline::execute::execute_have_fn_equal_case_by_case_stmt::{
    ExecHaveFnEqualCaseByCaseStmtResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::result::{
    ExecDefAlgoByCasesStmtFailed, ExecDefAlgoByCasesStmtResult,
    ExecDefAlgoByCasesStmtSuccessResult,
};

pub fn exec_def_algo_by_cases_stmt(
    runtime: &mut Runtime,
    stmt: &DefAlgoByCasesStmt,
) -> RuntimeResult<ExecDefAlgoByCasesStmtResult> {
    if runtime.def_algo_visible_in_stack(&stmt.name).is_some() {
        return Ok(ExecDefAlgoByCasesStmtResult::Failed(
            ExecDefAlgoByCasesStmtFailed::AlgoAlreadyDefined,
        ));
    }

    let have_stmt = HaveFnEqualCaseByCaseStmt {
        name: stmt.name.clone(),
        fn_set_clause: stmt.fn_set_clause.clone(),
        cases: stmt.cases.clone(),
        equal_tos: stmt.equal_tos.clone(),
        line_file: stmt.line_file.clone(),
    };

    match runtime.exec_have_fn_equal_case_by_case_stmt(&have_stmt)? {
        ExecHaveFnEqualCaseByCaseStmtResult::Failed(failed) => {
            Ok(ExecDefAlgoByCasesStmtResult::Failed(
                ExecDefAlgoByCasesStmtFailed::DefineFn(failed),
            ))
        }
        ExecHaveFnEqualCaseByCaseStmtResult::Success(define_fn) => {
            runtime
                .top_exec_env_mut()
                .store_def_algo(StoredDefAlgo::ByCases(stmt.clone()));
            Ok(ExecDefAlgoByCasesStmtResult::Success(
                ExecDefAlgoByCasesStmtSuccessResult {
                    statement: stmt.clone(),
                    define_fn,
                },
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::new_pipeline::execute::exec_stmt_result::{
        ExecDefinitionStmtResult, ExecStmtResult,
    };
    use crate::new_pipeline::execute::execute_have_fn_equal_case_by_case_stmt::ExecHaveFnEqualCaseByCaseStmtFailed;
    use crate::new_pipeline::launch_command::LaunchCommand;
    use crate::new_pipeline::runtime::Runtime;
    use crate::new_pipeline::tokenize::Tokenizer;

    fn runtime_with_file_env() -> Runtime {
        Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: false,
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
        let r = exec_one(
            &mut runtime,
            "algo g(x R) R by cases:\n    case x = 0: 0",
        );
        match r {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAlgoByCases(
                ExecDefAlgoByCasesStmtResult::Failed(ExecDefAlgoByCasesStmtFailed::DefineFn(
                    ExecHaveFnEqualCaseByCaseStmtFailed::Coverage(_),
                )),
            )) => {}
            other => panic!("expected coverage DefineFn fail, got failed={}", other.is_failed()),
        }
    }

    #[test]
    fn def_algo_by_cases_via_run_eval_like_cli() {
        use crate::new_pipeline::run::run_eval::run_eval;
        let code = "algo nonzero_flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1\n\neval nonzero_flag(0)";
        let result = run_eval(LaunchCommand::Eval {
            code: code.to_string(),
            session: false,
            strict: false,
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
}
