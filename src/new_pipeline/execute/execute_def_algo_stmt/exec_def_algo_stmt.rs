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