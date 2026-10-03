use crate::ast::fact::Fact;
use crate::ast::stmt::DefStrategyStmt;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_by_stmt::{
    proof_verify_state, verify_goal_fact,
};
use crate::execute::ExecStmtResult;
use crate::execute::execute_proof_block_stmt::{run_proof_body_stmts, ProofBlockBodyFailed};
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::runtime::{Runtime, RuntimeResult};

// strategy Name: ? forall … — prove the forall in a local body and store the
// named interface under strategy_definitions.
//
// The proved forall is NOT injected into ordinary known_forall matching.
// Later atomic goals use it via the dedicated known_strategy search stage.
//
// Example:
//   prop is_one(x R):
//       x = 1
//   strategy use_is_one:
//       ? forall x R:
//           x = 1
//           =>:
//               $is_one(x)
//       $is_one(x)

pub enum ExecDefStrategyStmtResult {
    Success(ExecDefStrategyStmtSuccess),
    Failed(ExecDefStrategyStmtFailed),
}

pub struct ExecDefStrategyStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub proof_steps: Vec<ExecStmtResult>,
    pub conclusion_proofs: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
}

pub enum ExecDefStrategyStmtFailed {
    NameClash(String),
    GoalWd(VerifyFactWellDefinedResult),
    Introduce(String),
    ProofBody(ProofBlockBodyFailed),
    Conclusion {
        index: usize,
        result: VerifyFactResult,
    },
}

impl ExecDefStrategyStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn exec_def_strategy_stmt(
    runtime: &mut Runtime,
    stmt: &DefStrategyStmt,
) -> RuntimeResult<ExecDefStrategyStmtResult> {
    if runtime.def_thm_visible_in_stack(&stmt.name).is_some()
        || runtime.axiom_visible_in_stack(&stmt.name).is_some()
        || runtime.def_strategy_visible_in_stack(&stmt.name).is_some()
    {
        return Ok(ExecDefStrategyStmtResult::Failed(
            ExecDefStrategyStmtFailed::NameClash(format!(
                "strategy `{}` is already defined",
                stmt.name
            )),
        ));
    }

    let goal: Fact = Fact::ForallFact(stmt.forall_fact.clone());
    let goal_wd = runtime.verify_fact_well_definedness(&goal, proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(ExecDefStrategyStmtResult::Failed(
            ExecDefStrategyStmtFailed::GoalWd(goal_wd),
        ));
    }

    let (local_outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
        exec_def_strategy_forall_body(rt, &stmt.forall_fact, &stmt.prove_process)
    })?;

    let (proof_steps, conclusion_proofs) = match local_outcome {
        Ok(v) => v,
        Err(failed) => return Ok(ExecDefStrategyStmtResult::Failed(failed)),
    };

    runtime.top_exec_env_mut().store_def_strategy(stmt.clone());

    Ok(ExecDefStrategyStmtResult::Success(ExecDefStrategyStmtSuccess {
        goal_wd,
        proof_steps,
        conclusion_proofs,
        local_env,
    }))
}

fn exec_def_strategy_forall_body(
    runtime: &mut Runtime,
    forall: &crate::ast::fact::ForallFact,
    proof: &[crate::ast::stmt::Stmt],
) -> RuntimeResult<
    Result<(Vec<ExecStmtResult>, Vec<VerifyFactResult>), ExecDefStrategyStmtFailed>,
> {
    if runtime
        .introduce_typed_parameters(&forall.typed_parameters, proof_verify_state())?
        .is_err()
    {
        return Ok(Err(ExecDefStrategyStmtFailed::Introduce(
            "strategy: failed to introduce forall parameters".to_string(),
        )));
    }

    for dom in &forall.dom_facts {
        let wd = runtime.verify_fact_well_definedness(dom, proof_verify_state())?;
        if wd.is_failed() {
            return Ok(Err(ExecDefStrategyStmtFailed::Introduce(
                "strategy: forall domain fact is not well-defined".to_string(),
            )));
        }
        let _ = runtime.store_fact_and_infer(dom, crate::execute::execute_fact_stmt::VerifyState::top_level())?;
    }

    let proof_steps = match run_proof_body_stmts(runtime, proof)? {
        Ok(steps) => steps,
        Err(failed) => return Ok(Err(ExecDefStrategyStmtFailed::ProofBody(failed))),
    };

    let mut conclusion_proofs = Vec::with_capacity(forall.then_facts.len());
    for (index, then) in forall.then_facts.iter().enumerate() {
        let then_fact: Fact = then.clone().into();
        let proof = verify_goal_fact(runtime, &then_fact)?;
        if proof.is_failed() {
            return Ok(Err(ExecDefStrategyStmtFailed::Conclusion {
                index,
                result: proof,
            }));
        }
        conclusion_proofs.push(proof);
    }

    Ok(Ok((proof_steps, conclusion_proofs)))
}
