use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::ast::stmt::AxiomStmt;
use crate::new_pipeline::execute::execute_by_stmt::{proof_verify_state, store_goal_fact};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyFactWellDefinedResult;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

// axiom Name: ? forall … — check goal WD, store the named interface, and inject
// the forall into ambient known facts (no proof body; truth is trusted).
//
// Example:
//   axiom eq_refl:
//       ? forall x R:
//           x = x
//   1 = 1

pub enum ExecAxiomStmtResult {
    Success(ExecAxiomStmtSuccess),
    Failed(ExecAxiomStmtFailed),
}

pub struct ExecAxiomStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecAxiomStmtFailed {
    NameClash(String),
    GoalWd(VerifyFactWellDefinedResult),
    Store(String),
}

impl ExecAxiomStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn exec_axiom_stmt(
    runtime: &mut Runtime,
    stmt: &AxiomStmt,
) -> RuntimeResult<ExecAxiomStmtResult> {
    if runtime.def_thm_visible_in_stack(&stmt.name).is_some()
        || runtime.axiom_visible_in_stack(&stmt.name).is_some()
        || runtime.def_strategy_visible_in_stack(&stmt.name).is_some()
    {
        return Ok(ExecAxiomStmtResult::Failed(ExecAxiomStmtFailed::NameClash(
            format!("axiom `{}` is already defined", stmt.name),
        )));
    }

    let goal = Fact::ForallFact(stmt.forall_fact.clone());
    let goal_wd = runtime.verify_fact_well_definedness(&goal, proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(ExecAxiomStmtResult::Failed(ExecAxiomStmtFailed::GoalWd(
            goal_wd,
        )));
    }

    runtime.top_exec_env_mut().store_axiom(stmt.clone());

    let stored = match store_goal_fact(runtime, &goal)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecAxiomStmtResult::Failed(ExecAxiomStmtFailed::Store(msg)));
        }
    };

    Ok(ExecAxiomStmtResult::Success(ExecAxiomStmtSuccess {
        goal_wd,
        stored,
    }))
}
