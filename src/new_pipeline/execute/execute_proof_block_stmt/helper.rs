use super::result::ProofBlockBodyFailed;
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::ast::stmt::Stmt;
use crate::new_pipeline::execute::exec_stmt_result::ExecStmtResult;
use crate::new_pipeline::execute::execute_by_stmt::{
    proof_verify_state, store_goal_fact, verify_goal_fact,
};
use crate::new_pipeline::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

// Run each body stmt through `exec_stmt` so helpers get the usual temp merge
// into the current (claim/sketch) local env. Soft-fail lifts to ProofBody.
pub(super) fn run_proof_body_stmts(
    runtime: &mut Runtime,
    proof: &[Stmt],
) -> RuntimeResult<Result<Vec<ExecStmtResult>, ProofBlockBodyFailed>> {
    let mut steps = Vec::with_capacity(proof.len());
    for (step_index, stmt) in proof.iter().enumerate() {
        let result = runtime.exec_stmt(stmt)?;
        if result.is_failed() {
            return Ok(Err(ProofBlockBodyFailed {
                step_index,
                result: Box::new(result),
            }));
        }
        steps.push(result);
    }
    Ok(Ok(steps))
}

pub(super) fn claim_proof_verify_state() -> VerifyState {
    proof_verify_state()
}

pub(super) fn claim_store_goal_fact(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<Result<StoreFactAndInferResult, String>> {
    store_goal_fact(runtime, fact)
}

pub(super) fn claim_verify_goal_fact(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<VerifyFactResult> {
    verify_goal_fact(runtime, fact)
}
