use super::enumerate_forall::{exec_enumerate_forall_goal, EnumerateForallFailed};
use super::result::{
    ExecByForStmtFailed, ExecByForStmtResult, ExecByForStmtSuccess, ExecByStmtResult,
};
use crate::ast::stmt::ByForStmt;
use crate::runtime::{Runtime, RuntimeResult};

pub fn exec_by_for_stmt(
    runtime: &mut Runtime,
    stmt: &ByForStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let outcome = exec_enumerate_forall_goal(runtime, &stmt.forall_fact, &stmt.proof)?;
    match outcome {
        Ok(success) => Ok(ExecByStmtResult::For(ExecByForStmtResult::Success(
            ExecByForStmtSuccess {
                goal_wd: success.goal_wd,
                assignments: success.assignments,
                stored: success.stored,
            },
        ))),
        Err(failed) => Ok(ExecByStmtResult::For(ExecByForStmtResult::Failed(
            map_failed(failed),
        ))),
    }
}

fn map_failed(failed: EnumerateForallFailed) -> ExecByForStmtFailed {
    match failed {
        EnumerateForallFailed::GoalWd(r) => ExecByForStmtFailed::GoalWd(r),
        EnumerateForallFailed::Domain(s) => ExecByForStmtFailed::Domain(s),
        EnumerateForallFailed::ProofBody(_b) => {
            ExecByForStmtFailed::Domain("proof body failed".to_string())
        }
        EnumerateForallFailed::Assignment {
            index,
            then_index,
            result,
        } => ExecByForStmtFailed::Assignment {
            index,
            then_index,
            result,
        },
        EnumerateForallFailed::Instantiate(s) => ExecByForStmtFailed::Instantiate(s),
        EnumerateForallFailed::Store(s) => ExecByForStmtFailed::Store(s),
    }
}
