use super::helper::{
    assume_fact, close_by_contradiction, negate_fact_for_contra, proof_verify_state,
    store_goal_fact,
};
use super::result::{
    ExecByContraStmtFailed, ExecByContraStmtResult, ExecByContraStmtSuccess, ExecByStmtResult,
};
use crate::ast::stmt::ByContraStmt;
use crate::execute::execute_proof_block_stmt::run_proof_body_stmts;
use crate::runtime::{Runtime, RuntimeResult};

pub fn exec_by_contra_stmt(
    runtime: &mut Runtime,
    stmt: &ByContraStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let goal_wd = runtime.verify_fact_well_definedness(&stmt.to_prove, proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
            ExecByContraStmtFailed::GoalWd(goal_wd),
        )));
    }

    let negation = match negate_fact_for_contra(runtime, &stmt.to_prove) {
        Ok(f) => f,
        Err(msg) => {
            return Ok(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
                ExecByContraStmtFailed::NegationUnsupported(msg),
            )));
        }
    };

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let negation_assumed = match assume_fact(rt, &negation)? {
            Ok(stored) => stored,
            Err(msg) => return Ok(Err(ExecByContraStmtFailed::NegationAssume(msg))),
        };
        let reverse_assumption_fact_id = negation_assumed.primary_fact_id();
        let assumption_components = negation_assumed.atomic_components();
        let proof_steps = match run_proof_body_stmts(rt, &stmt.proof)? {
            Ok(steps) => steps,
            Err(failed) => return Ok(Err(ExecByContraStmtFailed::ProofBody(failed))),
        };
        let closing = match close_by_contradiction(rt, &stmt.impossible_fact)? {
            Ok(c) => c,
            Err(failed) => return Ok(Err(ExecByContraStmtFailed::Closing(failed))),
        };
        Ok(Ok((
            negation_assumed,
            reverse_assumption_fact_id,
            assumption_components,
            proof_steps,
            closing,
        )))
    })?;

    let (negation_assumed, reverse_assumption_fact_id, assumption_components, proof_steps, closing) =
        match local_outcome {
            Ok(v) => v,
            Err(failed) => {
                return Ok(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
                    failed,
                )));
            }
        };

    let stored = match store_goal_fact(runtime, &stmt.to_prove)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
                ExecByContraStmtFailed::Store(msg),
            )));
        }
    };

    Ok(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(
        ExecByContraStmtSuccess {
            goal_wd,
            goal: stmt.to_prove.clone(),
            reverse_assumption: negation,
            reverse_assumption_fact_id,
            assumption_components,
            negation_assumed,
            proof_steps,
            closing,
            local_env,
            stored,
        },
    )))
}
