use super::enumerate_helpers::{cartesian_assignments, forall_param_domains};
use super::helper::{proof_verify_state, run_fact_only_proof_steps, store_goal_fact, verify_goal_fact};
use super::result::{ByProofBodyFailed, EnumerateAssignmentSuccess};
use crate::ast::fact::{Fact, ForallFact};
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub(super) enum EnumerateForallFailed {
    GoalWd(VerifyFactWellDefinedResult),
    Domain(String),
    ProofBody(ByProofBodyFailed),
    Assignment {
        index: usize,
        then_index: usize,
        result: VerifyFactResult,
    },
    Instantiate(String),
    Store(String),
}

pub(super) struct EnumerateForallSuccess {
    pub goal_wd: VerifyFactWellDefinedResult,
    pub assignments: Vec<EnumerateAssignmentSuccess>,
    pub stored: StoreFactAndInferResult,
}

pub(super) fn exec_enumerate_forall_goal(
    runtime: &mut Runtime,
    forall: &ForallFact,
    proof: &[Stmt],
) -> RuntimeResult<Result<EnumerateForallSuccess, EnumerateForallFailed>> {
    let goal = Fact::ForallFact(forall.clone());
    let goal_wd = runtime.verify_fact_well_definedness(&goal, proof_verify_state())?;
    if goal_wd.is_failed() {
        return Ok(Err(EnumerateForallFailed::GoalWd(goal_wd)));
    }

    let domains = match forall_param_domains(forall) {
        Ok(d) => d,
        Err(msg) => return Ok(Err(EnumerateForallFailed::Domain(msg))),
    };
    let assignments_maps = cartesian_assignments(&domains);

    let mut assignments = Vec::with_capacity(assignments_maps.len());
    for (index, subst) in assignments_maps.into_iter().enumerate() {
        let (outcome, local_env) = runtime.run_in_local_env_and_take_env(|rt| {
            if !proof.is_empty() {
                match run_fact_only_proof_steps(rt, proof)? {
                    Ok(_) => {}
                    Err(failed) => return Ok(Err(EnumerateForallFailed::ProofBody(failed))),
                }
            }
            let mut then_proofs = Vec::with_capacity(forall.then_facts.len());
            for (then_index, then) in forall.then_facts.iter().enumerate() {
                let then_fact: Fact = then.clone().into();
                let instantiated = match rt.inst_fact(&then_fact, &subst) {
                    Ok(f) => f,
                    Err(err) => {
                        return Ok(Err(EnumerateForallFailed::Instantiate(err.to_string())));
                    }
                };
                let proof = verify_goal_fact(rt, &instantiated)?;
                if proof.is_failed() {
                    return Ok(Err(EnumerateForallFailed::Assignment {
                        index,
                        then_index,
                        result: proof,
                    }));
                }
                then_proofs.push(proof);
            }
            Ok(Ok(then_proofs))
        })?;

        let then_proofs = match outcome {
            Ok(v) => v,
            Err(failed) => return Ok(Err(failed)),
        };
        assignments.push(EnumerateAssignmentSuccess {
            then_proofs,
            local_env,
        });
    }

    let stored = match store_goal_fact(runtime, &goal)? {
        Ok(s) => s,
        Err(msg) => return Ok(Err(EnumerateForallFailed::Store(msg))),
    };

    Ok(Ok(EnumerateForallSuccess {
        goal_wd,
        assignments,
        stored,
    }))
}
