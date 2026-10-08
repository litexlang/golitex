use super::helper::{proof_verify_state, store_goal_fact};
use super::result::{
    ExecByDefStmtFailed, ExecByDefStmtResult, ExecByDefStmtSuccess, ExecByStmtResult,
};
use crate::ast::fact::Fact;
use crate::ast::stmt::ByDefStmt;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::{
    atomic_except_equality_fact_result_from_success,
    atomic_except_equality_fact_result_from_wd_fail,
    AtomicExceptEqualityFactSearchedProof,
};
use crate::execute::execute_fact_stmt::VerifyAtomicFactWellDefinedResult;
use crate::runtime::{Runtime, RuntimeResult};

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
        // Explicit definition requests must recheck the defining clauses even
        // when ordinary search can prove (or already knows) the target.
        let Some(definition) = rt.search_atomic_except_equality_fact_proof_by_definition(
            &stmt.fact,
            proof_verify_state(),
        )?
        else {
            return Ok(Err(ExecByDefStmtFailed::DefinitionUnavailable));
        };
        let well_defined =
            match rt.verify_atomic_fact_well_definedness(&stmt.fact, proof_verify_state())? {
                VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
                VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                    return Ok(Err(ExecByDefStmtFailed::Proof(
                        atomic_except_equality_fact_result_from_wd_fail(reason),
                    )));
                }
            };
        let proof = atomic_except_equality_fact_result_from_success(
            &stmt.fact,
            well_defined,
            AtomicExceptEqualityFactSearchedProof::ByDefinition(definition),
        );
        Ok(Ok(proof))
    })?;

    let proof = match proof_outcome {
        Ok(p) => p,
        Err(failed) => {
            return Ok(ExecByStmtResult::Def(ExecByDefStmtResult::Failed(failed)));
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
