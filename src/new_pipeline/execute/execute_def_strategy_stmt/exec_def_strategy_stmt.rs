use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::ast::stmt::DefStrategyStmt;
use crate::new_pipeline::exec_env::exec_env::ExecEnv;
use crate::new_pipeline::execute::execute_by_stmt::{
    proof_verify_state, run_fact_only_proof_steps, store_goal_fact, verify_goal_fact,
    ByProofBodyFailed, ByProofStepResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

// strategy Name: ? forall … — prove the forall (fact-only body), store the named
// interface, and inject the forall into ordinary known-fact matching.
//
// No separate strategy search channel and no activation state.
// Shape restriction ("restricted atomic") is not enforced here; any well-formed
// forall goal is accepted (same proof path as thm's forall branch).
//
// Example:
//   strategy refl_on_r:
//       ? forall x R:
//           x = x
//   # later: known forall matching may use this fact

pub enum ExecDefStrategyStmtResult {
    Success(ExecDefStrategyStmtSuccess),
    Failed(ExecDefStrategyStmtFailed),
}

pub struct ExecDefStrategyStmtSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub proof_steps: Vec<ByProofStepResult>,
    pub conclusion_proofs: Vec<VerifyFactResult>,
    pub local_env: Box<ExecEnv>,
    pub stored: StoreFactAndInferResult,
}

pub enum ExecDefStrategyStmtFailed {
    NameClash(String),
    GoalWd(VerifyFactWellDefinedResult),
    Introduce(String),
    ProofBody(ByProofBodyFailed),
    Conclusion {
        index: usize,
        result: VerifyFactResult,
    },
    Store(String),
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

    let stored = match store_goal_fact(runtime, &goal)? {
        Ok(s) => s,
        Err(msg) => {
            return Ok(ExecDefStrategyStmtResult::Failed(
                ExecDefStrategyStmtFailed::Store(msg),
            ));
        }
    };

    Ok(ExecDefStrategyStmtResult::Success(ExecDefStrategyStmtSuccess {
        goal_wd,
        proof_steps,
        conclusion_proofs,
        local_env,
        stored,
    }))
}

fn exec_def_strategy_forall_body(
    runtime: &mut Runtime,
    forall: &crate::new_pipeline::ast::fact::ForallFact,
    proof: &[crate::new_pipeline::ast::stmt::Stmt],
) -> RuntimeResult<
    Result<(Vec<ByProofStepResult>, Vec<VerifyFactResult>), ExecDefStrategyStmtFailed>,
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
        let _ = runtime.store_fact_and_infer(dom)?;
    }

    let proof_steps = match run_fact_only_proof_steps(runtime, proof)? {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::new_pipeline::execute::exec_stmt_result::{
        ExecDefinitionStmtResult, ExecStmtResult,
    };
    use crate::new_pipeline::launch_command::LaunchCommand;
    use crate::new_pipeline::tokenize::Tokenizer;

    fn runtime_with_file_env() -> Runtime {
        Runtime::new(LaunchCommand::Eval {
            code: String::new(),
            session: false,
            strict: false,
        })
    }

    fn exec_one(runtime: &mut Runtime, code: &str) -> ExecStmtResult {
        let tokens = Tokenizer::new()
            .tokenize(code, runtime.current_file.clone())
            .expect("tokenize");
        let stmts = runtime.parse(&tokens).expect("parse");
        assert_eq!(stmts.len(), 1, "expected exactly one stmt in:\n{code}");
        runtime
            .exec_stmt(&stmts[0])
            .expect("exec_stmt RuntimeResult")
    }

    #[test]
    fn def_strategy_forall_refl_succeeds() {
        let mut runtime = runtime_with_file_env();
        let code = "strategy refl_on_r:\n    ? forall x R:\n        x = x";
        let r = exec_one(&mut runtime, code);
        match &r {
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
                ExecDefStrategyStmtResult::Success(_),
            )) => {}
            ExecStmtResult::Definition(ExecDefinitionStmtResult::DefStrategy(
                ExecDefStrategyStmtResult::Failed(f),
            )) => {
                let kind = match f {
                    ExecDefStrategyStmtFailed::NameClash(msg) => format!("NameClash:{msg}"),
                    ExecDefStrategyStmtFailed::GoalWd(_) => "GoalWd".to_string(),
                    ExecDefStrategyStmtFailed::Introduce(msg) => format!("Introduce:{msg}"),
                    ExecDefStrategyStmtFailed::ProofBody(_) => "ProofBody".to_string(),
                    ExecDefStrategyStmtFailed::Conclusion { index, .. } => {
                        format!("Conclusion:{index}")
                    }
                    ExecDefStrategyStmtFailed::Store(msg) => format!("Store:{msg}"),
                };
                panic!("strategy failed: {kind}")
            }
            other => panic!("unexpected result: failed={}", other.is_failed()),
        }
        assert!(runtime.def_strategy_visible_in_stack("refl_on_r").is_some());
    }
}

