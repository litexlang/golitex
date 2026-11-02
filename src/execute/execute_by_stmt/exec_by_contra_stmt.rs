use super::helper::{close_by_contradiction, negate_fact_for_contra, proof_verify_state};
use super::result::{
    ExecByContraStmtFailed, ExecByContraStmtResult, ExecByContraStmtSuccess, ExecByStmtResult,
};
use super::{
    ContraAssumption, ExecByContraEnteredFailed, ExecByContraLocalFailure, ExecByContraLocalProof,
    ExecByContraStoreFailure,
};
use crate::ast::stmt::ByContraStmt;
use crate::execute::execute_fact_stmt::{VerifyFactWellDefinedResult, VerifyState};
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
        Ok(fact) => fact,
        Err(message) => {
            return Ok(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
                ExecByContraStmtFailed::Negation(Box::new(
                    super::ExecByContraNegationFailure::new(stmt.clone(), goal_wd, message),
                )),
            )))
        }
    };

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        // The existing assume helper's verify/store stages, with its actual
        // failed WD result retained rather than reduced to a message.
        let result = rt.verify_fact_well_definedness(&negation, proof_verify_state())?;
        let VerifyFactWellDefinedResult::Success(well_defined) = result else {
            return Ok(Err(ExecByContraEnteredFailed::AssumptionWd(result)));
        };
        let stored = rt.store_fact_and_infer(&negation, VerifyState::top_level())?;
        let assumption = ContraAssumption::new(well_defined, stored);
        let proof_steps = match run_proof_body_stmts(rt, &stmt.proof)? {
            Ok(steps) => steps,
            Err(failure) => {
                return Ok(Err(ExecByContraEnteredFailed::ProofBody {
                    assumption,
                    failure,
                }))
            }
        };
        let closing = match close_by_contradiction(rt, &stmt.impossible_fact)? {
            Ok(proof) => proof,
            Err(failure) => {
                return Ok(Err(ExecByContraEnteredFailed::Closing {
                    assumption,
                    proof_steps,
                    failure,
                }))
            }
        };
        Ok(Ok(ExecByContraLocalProof::new(
            assumption,
            proof_steps,
            closing,
        )))
    })?;
    let proof = match local_outcome {
        Ok(proof) => proof,
        Err(failure) => {
            return Ok(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
                ExecByContraStmtFailed::Local(Box::new(ExecByContraLocalFailure::new(
                    stmt.clone(),
                    goal_wd,
                    negation,
                    failure,
                    local_env,
                ))),
            )))
        }
    };

    // Same final verify/store stages as store_goal_fact_with_wd. A failure here
    // owns the completed local proof and does not publish the original goal.
    let result = runtime.verify_fact_well_definedness(&stmt.to_prove, proof_verify_state())?;
    let VerifyFactWellDefinedResult::Success(stored_wd) = result else {
        return Ok(ExecByStmtResult::Contra(ExecByContraStmtResult::Failed(
            ExecByContraStmtFailed::StoreAfterProof(Box::new(ExecByContraStoreFailure::new(
                stmt.clone(),
                goal_wd,
                negation,
                proof,
                local_env,
                result,
            ))),
        )));
    };
    let stored = runtime.store_fact_and_infer(&stmt.to_prove, VerifyState::top_level())?;
    let ExecByContraLocalProof {
        assumption,
        proof_steps,
        closing,
    } = proof;
    let ContraAssumption {
        well_defined: reverse_assumption_wd,
        store_and_infer: negation_assumed,
        fact_id: reverse_assumption_fact_id,
        components: assumption_components,
    } = assumption;
    Ok(ExecByStmtResult::Contra(ExecByContraStmtResult::Success(
        ExecByContraStmtSuccess {
            goal_wd,
            goal: stmt.to_prove.clone(),
            reverse_assumption: negation,
            reverse_assumption_fact_id,
            assumption_components,
            reverse_assumption_wd,
            negation_assumed,
            proof_steps,
            closing,
            local_env,
            stored_wd,
            stored,
        },
    )))
}
