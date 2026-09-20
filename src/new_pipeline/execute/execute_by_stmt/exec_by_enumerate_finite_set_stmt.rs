use super::enumerate_forall::{exec_enumerate_forall_goal, EnumerateForallFailed};
use super::result::{
    ExecByEnumerateFiniteSetStmtFailed, ExecByEnumerateFiniteSetStmtResult,
    ExecByEnumerateFiniteSetStmtSuccess, ExecByStmtResult,
};
use crate::new_pipeline::ast::stmt::ByEnumerateFiniteSetStmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

pub fn exec_by_enumerate_finite_set_stmt(
    runtime: &mut Runtime,
    stmt: &ByEnumerateFiniteSetStmt,
) -> RuntimeResult<ExecByStmtResult> {
    let outcome = exec_enumerate_forall_goal(runtime, &stmt.forall_fact, &stmt.proof)?;
    match outcome {
        Ok(success) => Ok(ExecByStmtResult::EnumerateFiniteSet(
            ExecByEnumerateFiniteSetStmtResult::Success(ExecByEnumerateFiniteSetStmtSuccess {
                goal_wd: success.goal_wd,
                assignments: success.assignments,
                stored: success.stored,
            }),
        )),
        Err(failed) => Ok(ExecByStmtResult::EnumerateFiniteSet(
            ExecByEnumerateFiniteSetStmtResult::Failed(map_failed(failed)),
        )),
    }
}

fn map_failed(failed: EnumerateForallFailed) -> ExecByEnumerateFiniteSetStmtFailed {
    match failed {
        EnumerateForallFailed::GoalWd(r) => ExecByEnumerateFiniteSetStmtFailed::GoalWd(r),
        EnumerateForallFailed::Domain(s) => ExecByEnumerateFiniteSetStmtFailed::Domain(s),
        EnumerateForallFailed::ProofBody(_b) => {
            ExecByEnumerateFiniteSetStmtFailed::Domain("proof body failed".to_string())
        }
        EnumerateForallFailed::Assignment {
            index,
            then_index,
            result,
        } => ExecByEnumerateFiniteSetStmtFailed::Assignment {
            index,
            then_index,
            result,
        },
        EnumerateForallFailed::Instantiate(s) => ExecByEnumerateFiniteSetStmtFailed::Instantiate(s),
        EnumerateForallFailed::Store(s) => ExecByEnumerateFiniteSetStmtFailed::Store(s),
    }
}

