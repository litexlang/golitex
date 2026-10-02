use crate::execute::execute_proof_block_stmt::run_proof_body_stmts;
use super::helper::{
    proof_verify_state, store_goal_fact, verify_goal_fact,
};
use super::result::{
    ExecByExtensionStmtFailed, ExecByExtensionStmtResult, ExecByExtensionStmtSuccess,
    ExecByStmtResult,
};
use crate::ast::fact::{EqualFact, Fact, SubsetFact};
use crate::ast::stmt::ByExtensionStmt;
use crate::runtime::{Runtime, RuntimeResult};

// `by extension`: prove equality from both subset directions (pure-set object equality).
pub fn exec_by_extension_stmt(
    runtime: &mut Runtime,
    stmt: &ByExtensionStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let goal: Fact = EqualFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: stmt.left.clone(),
        right: stmt.right.clone(),
        line_file: Some(stmt.line_file.clone()),
    }
    .into();

    let goal_wd = runtime.verify_fact_well_definedness(&goal, proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(ExecByStmtResult::Extension(ExecByExtensionStmtResult::Failed(
            ExecByExtensionStmtFailed::GoalWd(goal_wd),
        )));
    }

    let left_to_right: Fact = SubsetFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: stmt.left.clone(),
        right: stmt.right.clone(),
        line_file: Some(stmt.line_file.clone()),
    }
    .into();
    let right_to_left: Fact = SubsetFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        left: stmt.right.clone(),
        right: stmt.left.clone(),
        line_file: Some(stmt.line_file.clone()),
    }
    .into();

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let proof_steps = match run_proof_body_stmts(rt, &stmt.proof)? {
            Ok(steps) => steps,
            Err(failed) => return Ok(Err(ExecByExtensionStmtFailed::ProofBody(failed))),
        };
        let left_to_right_proof = verify_goal_fact(rt, &left_to_right)?;
        if left_to_right_proof.is_failed() {
            return Ok(Err(ExecByExtensionStmtFailed::LeftToRight(left_to_right_proof)));
        }
        let right_to_left_proof = verify_goal_fact(rt, &right_to_left)?;
        if right_to_left_proof.is_failed() {
            return Ok(Err(ExecByExtensionStmtFailed::RightToLeft(right_to_left_proof)));
        }
        Ok(Ok((proof_steps, left_to_right_proof, right_to_left_proof)))
    })?;

    let (proof_steps, left_to_right_proof, right_to_left_proof) = match local_outcome {
        Ok(v) => v,
        Err(failed) => {
            return Ok(ExecByStmtResult::Extension(ExecByExtensionStmtResult::Failed(
                failed,
            )));
        }
    };

    let stored = match store_goal_fact(runtime, &goal)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::Extension(ExecByExtensionStmtResult::Failed(
                ExecByExtensionStmtFailed::Store(msg),
            )));
        }
    };

    Ok(ExecByStmtResult::Extension(ExecByExtensionStmtResult::Success(
        ExecByExtensionStmtSuccess {
            goal_wd,
            proof_steps,
            left_to_right: left_to_right_proof,
            right_to_left: right_to_left_proof,
            local_env,
            stored,
        },
    )))
}
