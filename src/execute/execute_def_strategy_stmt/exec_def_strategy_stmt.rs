use super::{
    ExecDefStrategyEnteredFailed, ExecDefStrategyForallFailed, ExecDefStrategyLocalFailure,
};
use crate::ast::fact::Fact;
use crate::ast::stmt::DefStrategyStmt;
use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_by_stmt::{proof_verify_state, verify_goal_fact};
use crate::execute::execute_fact_stmt::{
    AssumeDomFactResult, VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::execute::execute_proof_block_stmt::run_proof_body_stmts;
use crate::execute::{ExecStmtResult, IntroduceTypedParametersResult};
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
    pub statement: DefStrategyStmt,
    pub goal_wd: VerifyFactWellDefinedResult,
    pub body: ExecDefStrategyForallProof,
    pub local_env: Box<ExecEnv>,
}

// Original local execution stages, in producer order. Goal WD introduces a
// separate temporary header and cannot replace these actual body FactIds.
pub struct ExecDefStrategyForallProof {
    pub introduced_params: IntroduceTypedParametersResult,
    pub assumed_dom_facts: Vec<AssumeDomFactResult>,
    pub proof_steps: Vec<ExecStmtResult>,
    pub conclusion_proofs: Vec<VerifyFactResult>,
}

pub enum ExecDefStrategyStmtFailed {
    NameClash(String),
    GoalWd(VerifyFactWellDefinedResult),
    Local(ExecDefStrategyLocalFailure),
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

    let body = match local_outcome {
        Ok(v) => v,
        Err(body) => {
            return Ok(ExecDefStrategyStmtResult::Failed(
                ExecDefStrategyStmtFailed::Local(ExecDefStrategyLocalFailure {
                    statement: stmt.clone(),
                    goal_wd,
                    body,
                    local_env,
                }),
            ))
        }
    };

    runtime.top_exec_env_mut().store_def_strategy(stmt.clone());

    Ok(ExecDefStrategyStmtResult::Success(
        ExecDefStrategyStmtSuccess {
            statement: stmt.clone(),
            goal_wd,
            body,
            local_env,
        },
    ))
}

fn exec_def_strategy_forall_body(
    runtime: &mut Runtime,
    forall: &crate::ast::fact::ForallFact,
    proof: &[crate::ast::stmt::Stmt],
) -> RuntimeResult<Result<ExecDefStrategyForallProof, ExecDefStrategyForallFailed>> {
    let introduced_params =
        match runtime.introduce_typed_parameters(&forall.typed_parameters, proof_verify_state())? {
            Ok(introduced) => introduced,
            Err(failed) => return Ok(Err(ExecDefStrategyForallFailed::Introduce(failed))),
        };

    let mut assumed_dom_facts = Vec::with_capacity(forall.dom_facts.len());
    for (index, dom) in forall.dom_facts.iter().enumerate() {
        let well_defined = match runtime.verify_fact_well_definedness(dom, proof_verify_state())? {
            VerifyFactWellDefinedResult::Success(wd) => wd,
            failed @ VerifyFactWellDefinedResult::Failed(_) => {
                return Ok(Err(ExecDefStrategyForallFailed::Entered {
                    introduced_params,
                    assumed_dom_facts,
                    failure: ExecDefStrategyEnteredFailed::PremiseWd {
                        index,
                        result: failed,
                    },
                }))
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
        Err(failed) => {
            return Ok(Err(ExecDefStrategyForallFailed::Entered {
                introduced_params,
                assumed_dom_facts,
                failure: ExecDefStrategyEnteredFailed::ProofBody(failed),
            }))
        }
    };

    let mut conclusion_proofs = Vec::with_capacity(forall.then_facts.len());
    for (index, then) in forall.then_facts.iter().enumerate() {
        let then_fact: Fact = then.clone().into();
        let proof = verify_goal_fact(runtime, &then_fact)?;
        if proof.is_failed() {
            return Ok(Err(ExecDefStrategyForallFailed::Entered {
                introduced_params,
                assumed_dom_facts,
                failure: ExecDefStrategyEnteredFailed::Conclusion {
                    proof_steps,
                    conclusion_proofs,
                    index,
                    result: proof,
                },
            }));
        }
        conclusion_proofs.push(proof);
    }

    Ok(Ok(ExecDefStrategyForallProof {
        introduced_params,
        assumed_dom_facts,
        proof_steps,
        conclusion_proofs,
    }))
}
