use super::enumerate_helpers::{cartesian_assignments, forall_param_domains};
use super::helper::{proof_verify_state, store_goal_fact, verify_goal_fact};
use super::result::{EnumerateAssignmentOutcome, EnumerateAssignmentSuccess};
use crate::ast::fact::{negate_atomic_fact, EqualFact, Fact, ForallFact};
use crate::ast::obj::Obj;
use crate::ast::stmt::Stmt;
use crate::execute::execute_fact_stmt::{
    AssumeDomFactResult, ProveAndStoreThenFactResult, VerifyFactResult, VerifyFactWellDefinedResult,
};
use crate::execute::execute_proof_block_stmt::{run_proof_body_stmts, ProofBlockBodyFailed};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub(super) enum EnumerateForallFailed {
    GoalWd(VerifyFactWellDefinedResult),
    Domain(String),
    ProofBody(ProofBlockBodyFailed),
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
            let introduced_params = match rt
                .introduce_typed_parameters(&forall.typed_parameters, proof_verify_state())?
            {
                Ok(introduced) => introduced,
                Err(_) => return Ok(Err(EnumerateForallFailed::Domain(
                    "enumeration parameter introduction failed".to_string(),
                ))),
            };
            // Each branch fixes the quantified parameters to one displayed assignment.
            // Keep the binders live so nested proof statements can use their names.
            let mut binding_assumptions = Vec::new();
            for group in &forall.typed_parameters.groups {
                for param in &group.params {
                    let Some(value) = subst.get(&param.id) else {
                        return Ok(Err(EnumerateForallFailed::Instantiate(
                            "missing enumeration assignment".to_string(),
                        )));
                    };
                    let equality: Fact = EqualFact {
                        fact_id: rt.global_ids.allocate_fact_id(),
                        left: Obj::Identifier(rt.identifier_obj_for_stored_mention(param)),
                        right: value.clone(),
                        line_file: forall.line_file.clone(),
                    }.into();
                    match assume_enumeration_fact(rt, &equality)? {
                        Ok(assumed) => binding_assumptions.push(assumed),
                        Err(failed) => return Ok(Err(failed)),
                    }
                }
            }

            let mut premise_assumptions = Vec::with_capacity(forall.dom_facts.len());
            for (premise_index, premise) in forall.dom_facts.iter().enumerate() {
                let instantiated = match rt.inst_fact(premise, &subst) {
                    Ok(fact) => fact,
                    Err(err) => return Ok(Err(EnumerateForallFailed::Instantiate(err.to_string()))),
                };
                // A proved false antecedent closes this implication vacuously.
                // Otherwise assume the antecedent locally; a failed negation is never a skip.
                if let Fact::AtomicFact(atomic) = &instantiated {
                    if let Some(negated) = negate_atomic_fact(atomic, rt.global_ids.allocate_fact_id()) {
                        let negated: Fact = negated.into();
                        let negated_premise = verify_goal_fact(rt, &negated)?;
                        if !negated_premise.is_failed() {
                            return Ok(Ok((introduced_params, binding_assumptions,
                                EnumerateAssignmentOutcome::Skipped {
                                    premise_assumptions, premise_index, negated_premise,
                                })));
                        }
                    }
                }
                match assume_enumeration_fact(rt, &instantiated)? {
                    Ok(assumed) => premise_assumptions.push(assumed),
                    Err(failed) => return Ok(Err(failed)),
                }
            }

            let proof_steps = match run_proof_body_stmts(rt, proof)? {
                Ok(steps) => steps,
                Err(failed) => return Ok(Err(EnumerateForallFailed::ProofBody(failed))),
            };
            let mut then_proofs = Vec::with_capacity(forall.then_facts.len());
            for (then_index, then) in forall.then_facts.iter().enumerate() {
                let then_fact: Fact = then.clone().into();
                let instantiated = match rt.inst_fact(&then_fact, &subst) {
                    Ok(f) => f,
                    Err(err) => return Ok(Err(EnumerateForallFailed::Instantiate(err.to_string()))),
                };
                let proof = verify_goal_fact(rt, &instantiated)?;
                if proof.is_failed() {
                    return Ok(Err(EnumerateForallFailed::Assignment {
                        index, then_index, result: proof,
                    }));
                }
                let store_and_infer = rt.store_fact_and_infer(&instantiated, crate::execute::execute_fact_stmt::VerifyState::top_level())?;
                then_proofs.push(ProveAndStoreThenFactResult { verify_result: proof, store_and_infer });
            }
            Ok(Ok((introduced_params, binding_assumptions,
                EnumerateAssignmentOutcome::Proved {
                    premise_assumptions, proof_steps, then_proofs,
                })))
        })?;

        let (introduced_params, binding_assumptions, outcome) = match outcome {
            Ok(v) => v,
            Err(failed) => return Ok(Err(failed)),
        };
        assignments.push(EnumerateAssignmentSuccess {
            introduced_params, binding_assumptions, outcome, local_env,
        });
    }

    let stored = match store_goal_fact(runtime, &goal)? {
        Ok(s) => s,
        Err(msg) => return Ok(Err(EnumerateForallFailed::Store(msg))),
    };

    Ok(Ok(EnumerateForallSuccess { goal_wd, assignments, stored }))
}

fn assume_enumeration_fact(
    runtime: &mut Runtime,
    fact: &Fact,
) -> RuntimeResult<Result<AssumeDomFactResult, EnumerateForallFailed>> {
    let well_defined = match runtime.verify_fact_well_definedness(fact, proof_verify_state())? {
        VerifyFactWellDefinedResult::Success(proof) => proof,
        failed => return Ok(Err(EnumerateForallFailed::GoalWd(failed))),
    };
    let store_and_infer = runtime.store_fact_and_infer(fact, crate::execute::execute_fact_stmt::VerifyState::top_level())?;
    Ok(Ok(AssumeDomFactResult { well_defined, store_and_infer }))
}
