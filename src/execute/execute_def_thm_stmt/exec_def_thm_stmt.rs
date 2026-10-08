use crate::ast::fact::{Fact, ForallFact};
use crate::ast::stmt::{DefThmStmt, Stmt};
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::exec_stmt_result::ExecStmtResult;
use crate::execute::execute_by_stmt::{proof_verify_state, store_goal_fact, verify_goal_fact};
use crate::execute::execute_fact_stmt::{
    AssumeDomFactResult, VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::execute::execute_proof_block_stmt::{run_proof_body_stmts, ProofBlockBodyFailed};
use crate::execute::IntroduceTypedParametersResult;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

// `local_env`: FactId/WdId resolution table for the theorem proof scope (same
// role as documented in execute_by_stmt/result.rs).

pub enum ExecDefThmStmtResult {
    Success(ExecDefThmStmtSuccess),
    Failed(ExecDefThmStmtFailed),
}

pub struct ExecDefThmStmtSuccess {
    pub statement: DefThmStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub body: ExecDefThmBodyProof,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

// Non-forall goals already include compound facts. Preserve that existing
// execution boundary rather than falsely classifying every direct goal atomic.
pub enum ExecDefThmBodyProof {
    NonForall(ExecDefThmNonForallProof),
    Forall(ExecDefThmForallProof),
}

pub struct ExecDefThmNonForallProof {
    pub proof_steps: Vec<ExecStmtResult>,
    pub conclusion_proof: VerifyFactResult,
}

pub struct ExecDefThmForallProof {
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub proof_steps: Vec<ExecStmtResult>,
    pub conclusion_proofs: Vec<VerifyFactResult>,
}

pub enum ExecDefThmStmtFailed {
    NameClash(String),
    GoalUnsupported(String),
    GoalWd(VerifyFactWellDefinedResult),
    Introduce(String),
    ProofBody(ProofBlockBodyFailed),
    Conclusion {
        index: usize,
        result: VerifyFactResult,
    },
    Store(String),
}

impl ExecDefThmStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

pub fn exec_def_thm_stmt(
    runtime: &mut Runtime,
    stmt: &DefThmStmt,
) -> RuntimeResult<ExecDefThmStmtResult> {
    if runtime.def_thm_visible_in_stack(&stmt.name).is_some()
        || runtime.axiom_visible_in_stack(&stmt.name).is_some()
        || runtime.def_strategy_visible_in_stack(&stmt.name).is_some()
    {
        return Ok(ExecDefThmStmtResult::Failed(
            ExecDefThmStmtFailed::NameClash(format!("thm `{}` is already defined", stmt.name)),
        ));
    }

    if matches!(stmt.fact, Fact::ForallFactWithIff(_)) {
        return Ok(ExecDefThmStmtFailed::GoalUnsupported(
            "thm: forall ... <=> goals are not supported".to_string(),
        )
        .into());
    }

    let goal_wd = runtime.verify_fact_well_definedness(&stmt.fact, proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(ExecDefThmStmtResult::Failed(ExecDefThmStmtFailed::GoalWd(
            goal_wd,
        )));
    }

    let (local_outcome, local_env) =
        runtime.run_in_local_env_and_take_env(|rt| match &stmt.fact {
            Fact::ForallFact(forall) => exec_def_thm_forall_body(rt, forall, &stmt.prove_process),
            _ => {
                let proof_steps = match run_proof_body_stmts(rt, &stmt.prove_process)? {
                    Ok(steps) => steps,
                    Err(failed) => return Ok(Err(ExecDefThmStmtFailed::ProofBody(failed))),
                };
                let proof = verify_goal_fact(rt, &stmt.fact)?;
                if proof.is_failed() {
                    return Ok(Err(ExecDefThmStmtFailed::Conclusion {
                        index: 0,
                        result: proof,
                    }));
                }
                Ok(Ok(ExecDefThmNonForallProof::new(proof_steps, proof).into()))
            }
        })?;

    let body = match local_outcome {
        Ok(v) => v,
        Err(failed) => return Ok(ExecDefThmStmtResult::Failed(failed)),
    };

    runtime.top_exec_env_mut().store_def_thm(stmt.clone());

    let stored = match store_goal_fact(runtime, &stmt.fact)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecDefThmStmtResult::Failed(ExecDefThmStmtFailed::Store(
                msg,
            )));
        }
    };

    Ok(ExecDefThmStmtSuccess::new(stmt.clone(), goal_wd, body, local_env, stored).into())
}

fn exec_def_thm_forall_body(
    runtime: &mut Runtime,
    forall: &ForallFact,
    proof: &[Stmt],
) -> RuntimeResult<Result<ExecDefThmBodyProof, ExecDefThmStmtFailed>> {
    let introduced_params =
        match runtime.introduce_typed_parameters(&forall.typed_parameters, proof_verify_state())? {
            Ok(introduced) => introduced,
            Err(_) => {
                return Ok(Err(ExecDefThmStmtFailed::Introduce(
                    "thm: failed to introduce forall parameters".to_string(),
                )))
            }
        };

    let mut assumed_dom_facts = Vec::with_capacity(forall.dom_facts.len());
    for dom in &forall.dom_facts {
        let well_defined = match runtime.verify_fact_well_definedness(dom, proof_verify_state())? {
            VerifyFactWellDefinedResult::Success(proof) => proof,
            VerifyFactWellDefinedResult::Failed(_) => {
                return Ok(Err(ExecDefThmStmtFailed::Introduce(
                    "thm: forall domain fact is not well-defined".to_string(),
                )))
            }
        };
        let store_and_infer = runtime.store_fact_and_infer(
            dom,
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        )?;
        assumed_dom_facts.push(AssumeDomFactResult {
            well_defined,
            store_and_infer,
        });
    }

    let proof_steps = match run_proof_body_stmts(runtime, proof)? {
        Ok(steps) => steps,
        Err(failed) => return Ok(Err(ExecDefThmStmtFailed::ProofBody(failed))),
    };

    let mut conclusion_proofs = Vec::with_capacity(forall.then_facts.len());
    for (index, then) in forall.then_facts.iter().enumerate() {
        let then_fact: Fact = then.clone().into();
        let proof = verify_goal_fact(runtime, &then_fact)?;
        if proof.is_failed() {
            return Ok(Err(ExecDefThmStmtFailed::Conclusion {
                index,
                result: proof,
            }));
        }
        conclusion_proofs.push(proof);
    }

    Ok(Ok(ExecDefThmForallProof::new(
        introduced_params,
        assumed_dom_facts,
        proof_steps,
        conclusion_proofs,
    )
    .into()))
}

impl ExecDefThmStmtSuccess {
    pub fn new(
        statement: DefThmStmt,
        goal_wd: VerifyFactWellDefinedResult,
        body: ExecDefThmBodyProof,
        local_env: Box<ExecEnv>,
        stored: StoreFactAndInferResult,
    ) -> Self {
        Self {
            statement,
            goal_wd,
            body,
            local_env,
            stored,
        }
    }
}

impl ExecDefThmNonForallProof {
    pub fn new(proof_steps: Vec<ExecStmtResult>, conclusion_proof: VerifyFactResult) -> Self {
        Self {
            proof_steps,
            conclusion_proof,
        }
    }
}

impl ExecDefThmForallProof {
    pub fn new(
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        proof_steps: Vec<ExecStmtResult>,
        conclusion_proofs: Vec<VerifyFactResult>,
    ) -> Self {
        Self {
            introduced_params,
            assumed_dom_facts,
            proof_steps,
            conclusion_proofs,
        }
    }
}

impl From<ExecDefThmStmtSuccess> for ExecDefThmStmtResult {
    fn from(success: ExecDefThmStmtSuccess) -> Self {
        Self::Success(success)
    }
}

impl From<ExecDefThmNonForallProof> for ExecDefThmBodyProof {
    fn from(proof: ExecDefThmNonForallProof) -> Self {
        Self::NonForall(proof)
    }
}

impl From<ExecDefThmForallProof> for ExecDefThmBodyProof {
    fn from(proof: ExecDefThmForallProof) -> Self {
        Self::Forall(proof)
    }
}

impl From<ExecDefThmStmtFailed> for ExecDefThmStmtResult {
    fn from(failed: ExecDefThmStmtFailed) -> Self {
        Self::Failed(failed)
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/execute/def_thm_goal_boundary/tests.rs"]
mod def_thm_goal_boundary_tests;

#[cfg(test)]
#[path = "../../../tests/unit/execute/def_thm_result_capture/tests.rs"]
mod def_thm_result_capture_tests;
