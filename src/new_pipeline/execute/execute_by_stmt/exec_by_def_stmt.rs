use super::helper::{proof_verify_state, store_goal_fact, verify_goal_fact};
use super::result::{
    ExecByDefStmtFailed, ExecByDefStmtResult, ExecByDefStmtSuccess, ExecByStmtResult,
};
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::ast::stmt::ByDefStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub fn exec_by_def_stmt(
    runtime: &mut Runtime,
    stmt: &ByDefStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let goal: Fact = stmt.fact.clone().into();
    let goal_wd = runtime.verify_fact_well_definedness(&goal, proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(ExecByStmtResult::Def(ExecByDefStmtResult::Failed(
            ExecByDefStmtFailed::GoalWd(goal_wd),
        )));
    }

    let (proof_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        let proof = verify_goal_fact(rt, &goal)?;
        if proof.is_failed() {
            return Ok(Err(proof));
        }
        Ok(Ok(proof))
    })?;

    let proof = match proof_outcome {
        Ok(p) => p,
        Err(failed) => {
            return Ok(ExecByStmtResult::Def(ExecByDefStmtResult::Failed(
                ExecByDefStmtFailed::Proof(failed),
            )));
        }
    };

    let stored = match store_goal_fact(runtime, &goal)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecByStmtResult::Def(ExecByDefStmtResult::Failed(
                ExecByDefStmtFailed::Store(msg),
            )));
        }
    };

    Ok(ExecByStmtResult::Def(ExecByDefStmtResult::Success(
        ExecByDefStmtSuccess {
            goal_wd,
            proof,
            local_env,
            stored,
        },
    )))
}
