//! `have algo for fn f(…):` — attach executable presentation; check agreement.

use crate::new_pipeline::ast::stmt::DefAlgoStmt;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::helper::{
    build_algo_setup, case_agreement_forall, coverage_forall, default_agreement_forall,
    resolve_target_fn_set,
};
use super::result::{
    ExecDefAlgoBranchAgreement, ExecDefAlgoCaseAgreement, ExecDefAlgoClosing,
    ExecDefAlgoCoverageAgreement, ExecDefAlgoStmtFailed, ExecDefAlgoStmtResult,
    ExecDefAlgoStmtSuccess,
};

pub fn exec_def_algo_stmt(
    runtime: &mut Runtime,
    stmt: &DefAlgoStmt,
) -> RuntimeResult<ExecDefAlgoStmtResult> {
    if runtime.def_algo_visible_in_stack(&stmt.name).is_some() {
        return Ok(ExecDefAlgoStmtResult::Failed(
            ExecDefAlgoStmtFailed::AlgoAlreadyDefined,
        ));
    }

    let (fn_set, _membership_fact_id) = match resolve_target_fn_set(runtime, stmt) {
        Ok(v) => v,
        Err(failed) => return Ok(ExecDefAlgoStmtResult::Failed(failed)),
    };

    let setup = match build_algo_setup(runtime, stmt, fn_set)? {
        Ok(s) => s,
        Err(failed) => return Ok(ExecDefAlgoStmtResult::Failed(failed)),
    };

    let verify_state = VerifyState {
        can_use_forall_fact: true,
        can_use_rewrite: true,
        store_well_defined_fact: true,
    };

    let mut cases = Vec::with_capacity(stmt.cases.len());
    for case_index in 0..stmt.cases.len() {
        let verification_fact = case_agreement_forall(runtime, stmt, &setup, case_index);
        let verification = runtime.verify_fact(&verification_fact, verify_state.clone())?;
        if verification.is_failed() {
            return Ok(ExecDefAlgoStmtResult::Failed(ExecDefAlgoStmtFailed::Case {
                case_index,
                verification_fact,
                verification,
            }));
        }
        cases.push(ExecDefAlgoCaseAgreement {
            case_index,
            verification_fact,
            verification,
        });
    }

    let closing = if stmt.default_return.is_some() {
        let verification_fact = match default_agreement_forall(runtime, stmt, &setup) {
            Ok(f) => f,
            Err(failed) => return Ok(ExecDefAlgoStmtResult::Failed(failed)),
        };
        let verification = runtime.verify_fact(&verification_fact, verify_state.clone())?;
        if verification.is_failed() {
            return Ok(ExecDefAlgoStmtResult::Failed(ExecDefAlgoStmtFailed::Default {
                verification_fact,
                verification,
            }));
        }
        ExecDefAlgoClosing::Default(ExecDefAlgoBranchAgreement {
            verification_fact,
            verification,
        })
    } else {
        let verification_fact = match coverage_forall(runtime, stmt, &setup) {
            Ok(f) => f,
            Err(failed) => return Ok(ExecDefAlgoStmtResult::Failed(failed)),
        };
        let verification = runtime.verify_fact(&verification_fact, verify_state)?;
        if verification.is_failed() {
            return Ok(ExecDefAlgoStmtResult::Failed(
                ExecDefAlgoStmtFailed::Coverage {
                    verification_fact,
                    verification,
                },
            ));
        }
        ExecDefAlgoClosing::Coverage(ExecDefAlgoCoverageAgreement {
            verification_fact,
            verification,
        })
    };

    runtime.top_exec_env_mut().store_def_algo(stmt.clone());

    Ok(ExecDefAlgoStmtResult::Success(ExecDefAlgoStmtSuccess {
        statement: stmt.clone(),
        setup,
        cases,
        closing,
    }))
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::new_pipeline::execute::exec_stmt_result::{
        ExecDefinitionStmtResult, ExecStmtResult,
    };
    use crate::new_pipeline::launch_command::LaunchCommand;
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
    fn def_algo_for_fn_by_cases_succeeds_and_stores() {
        let mut runtime = runtime_with_file_env();
        let have_fn = "have fn nonzero_flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1";
        assert!(
            !exec_one(&mut runtime, have_fn).is_failed(),
            "have fn by cases should succeed"
        );

        let algo = "have algo for fn nonzero_flag(x):\n    case x = 0: 0\n    case x != 0: 1";
        let r = exec_one(&mut runtime, algo);
        match &r {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAlgo(
                ExecDefAlgoStmtResult::Success(_),
            )) => {}
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAlgo(
                ExecDefAlgoStmtResult::Failed(f),
            )) => panic!("algo failed: {f:?}"),
            other => panic!("unexpected result: failed={}", other.is_failed()),
        }
        assert!(
            runtime.def_algo_visible_in_stack("nonzero_flag").is_some(),
            "algo should be stored"
        );
    }

    #[test]
    fn def_algo_mismatched_default_soft_fails() {
        let mut runtime = runtime_with_file_env();
        assert!(!exec_one(&mut runtime, "have fn f(x R) R = x").is_failed());
        let r = exec_one(&mut runtime, "have algo for fn f(x):\n    x + 1");
        match r {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAlgo(
                ExecDefAlgoStmtResult::Failed(ExecDefAlgoStmtFailed::Default { .. }),
            )) => {}
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAlgo(
                ExecDefAlgoStmtResult::Failed(other),
            )) => panic!("expected Default fail, got {other:?}"),
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefAlgo(
                ExecDefAlgoStmtResult::Success(_),
            )) => panic!("expected soft fail for mismatched algo"),
            other => panic!("unexpected result: failed={}", other.is_failed()),
        }
    }

    #[test]
    fn def_algo_via_run_eval_like_cli() {
        use crate::new_pipeline::run::run_eval::run_eval;
        let code = "have fn nonzero_flag(x R) R by cases:\n    case x = 0: 0\n    case x != 0: 1\n\nhave algo for fn nonzero_flag(x):\n    case x = 0: 0\n    case x != 0: 1";
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
