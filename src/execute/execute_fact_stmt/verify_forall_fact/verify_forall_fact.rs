use crate::ast::fact::{Fact, ForallFact};
use crate::ast::obj::{IdentifierObj, Obj};
use crate::ast::param::ParamType;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::{compound_objs_alpha_equal, quantifier_free_source_facts_alpha_equal};
use crate::execute::execute_fact_stmt::verify_forall_fact::result::{
    forall_fact_result_from_success, forall_fact_result_from_then_fail,
    forall_fact_result_from_wd_fail,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::FailToVerifyForallFactWellDefinedResult;
use crate::execute::execute_fact_stmt::verify_forall_fact::{
    AssumeDomFactResult, ForallParameterRenaming, ProveAndStoreThenFactResult,
    VerifyForallFactProof, VerifyForallFactResult, VerifyForallFactWellDefinedResult,
    VerifyKnownForallFactProof,
};
use crate::execute::execute_fact_stmt::well_defined_results::fail_to_verify_obj_well_defined_others;
use crate::execute::execute_fact_stmt::{
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::introduce_typed_parameters::{
    IntroduceTypedParametersFailed, IntroduceTypedParametersResult,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;
use std::collections::HashMap;

enum ForallLocalOutcome {
    Success {
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        proved_then_facts: Vec<ProveAndStoreThenFactResult>,
    },
    FailWd(FailToVerifyForallFactWellDefinedResult),
    FailThen {
        introduced_params: IntroduceTypedParametersResult,
        assumed_dom_facts: Vec<AssumeDomFactResult>,
        proved_then_facts: Vec<ProveAndStoreThenFactResult>,
        failed_then_index: usize,
        failed_then: VerifyFactResult,
    },
}

impl Runtime {
    // Prove forall by local introduction:
    //   introduce typed params → assume dom → prove+store each then → take local_env.
    // Soft miss → ForallFact(Failed); then-fact miss stays under ForallFact (unified).
    // Example:
    //   forall x R:
    //       x = x
    pub fn verify_forall_fact(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        // Reuse the entire proved proposition before projecting conclusions.
        // An unused binder is renamed positionally; it is never given a value.
        if let Some((cite_fact_id, parameter_renamings)) = self.match_known_forall_source(fact) {
            let well_defined =
                match self.verify_forall_fact_well_definedness(fact, verify_state.clone())? {
                    VerifyForallFactWellDefinedResult::Success(proof) => proof,
                    VerifyForallFactWellDefinedResult::Failed(reason) => {
                        return Ok(forall_fact_result_from_wd_fail(reason));
                    }
                };
            return Ok(VerifyFactResult::ForallFact(Box::new(
                VerifyForallFactResult::Success(VerifyForallFactProof::ByKnownForallFact(
                    VerifyKnownForallFactProof {
                        fact: fact.clone(),
                        well_defined,
                        cite_fact_id,
                        parameter_renamings,
                    },
                )),
            )));
        }
        let (local_outcome, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_forall_fact_in_local(fact, verify_state.clone())
        })?;

        match local_outcome {
            ForallLocalOutcome::Success {
                introduced_params,
                assumed_dom_facts,
                proved_then_facts,
            } => Ok(forall_fact_result_from_success(
                fact,
                introduced_params,
                assumed_dom_facts,
                proved_then_facts,
                local_env,
            )),
            ForallLocalOutcome::FailWd(reason) => Ok(forall_fact_result_from_wd_fail(reason)),
            ForallLocalOutcome::FailThen {
                introduced_params,
                assumed_dom_facts,
                proved_then_facts,
                failed_then_index,
                failed_then,
            } => Ok(forall_fact_result_from_then_fail(
                fact,
                introduced_params,
                assumed_dom_facts,
                proved_then_facts,
                failed_then_index,
                failed_then,
                local_env,
            )),
        }
    }

    pub(crate) fn match_known_forall_source(
        &mut self,
        goal: &ForallFact,
    ) -> Option<(crate::runtime::FactId, Vec<ForallParameterRenaming>)> {
        let sources: Vec<_> = self
            .execution_environments_stack
            .iter()
            .rev()
            .flat_map(|env| env.facts.facts_by_id.iter())
            .filter_map(|(id, fact)| match fact {
                Fact::ForallFact(source) => Some((*id, source.clone())),
                _ => None,
            })
            .collect();
        for (id, source) in sources {
            let source_bindings: Vec<_> = source
                .typed_parameters
                .groups
                .iter()
                .flat_map(|g| g.params.iter().map(|p| (p, &g.param_type)))
                .collect();
            let goal_bindings: Vec<_> = goal
                .typed_parameters
                .groups
                .iter()
                .flat_map(|g| g.params.iter().map(|p| (p, &g.param_type)))
                .collect();
            if source_bindings.len() != goal_bindings.len()
                || source.dom_facts.len() != goal.dom_facts.len()
                || source.then_facts.len() != goal.then_facts.len()
            {
                continue;
            }
            let subst: HashMap<_, _> = source_bindings
                .iter()
                .zip(&goal_bindings)
                .map(|((src, _), (dst, _))| {
                    (src.id, Obj::Identifier(IdentifierObj::from_bound_name(dst)))
                })
                .collect();
            let types_match =
                source_bindings
                    .iter()
                    .zip(&goal_bindings)
                    .all(
                        |((_, src), (_, dst))| match self.inst_param_type(src, &subst) {
                            Ok(inst) => match (&inst, *dst) {
                                (ParamType::Obj(a), ParamType::Obj(b)) => {
                                    compound_objs_alpha_equal(a, b)
                                }
                                (ParamType::Set(_), ParamType::Set(_))
                                | (ParamType::NonemptySet(_), ParamType::NonemptySet(_))
                                | (ParamType::FiniteSet(_), ParamType::FiniteSet(_)) => true,
                                _ => false,
                            },
                            Err(_) => false,
                        },
                    );
            if !types_match {
                continue;
            }
            let facts_match = source
                .dom_facts
                .iter()
                .zip(&goal.dom_facts)
                .all(|(src, dst)| {
                    self.inst_fact(src, &subst)
                        .ok()
                        .is_some_and(|inst| same_quantified_source_fact(&inst, dst))
                })
                && source
                    .then_facts
                    .iter()
                    .zip(&goal.then_facts)
                    .all(|(src, dst)| {
                        self.inst_fact(&Fact::from(src.clone()), &subst)
                            .ok()
                            .is_some_and(|inst| {
                                same_quantified_source_fact(&inst, &Fact::from(dst.clone()))
                            })
                    });
            if facts_match {
                let parameter_renamings = source_bindings
                    .iter()
                    .zip(&goal_bindings)
                    .map(|((src, _), (dst, _))| ForallParameterRenaming {
                        source: src.id,
                        target: dst.id,
                    })
                    .collect();
                return Some((id, parameter_renamings));
            }
        }
        None
    }

    fn verify_forall_fact_in_local(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<ForallLocalOutcome> {
        let introduced_params =
            match self.introduce_typed_parameters(&fact.typed_parameters, verify_state.clone())? {
                Ok(result) => result,
                Err(IntroduceTypedParametersFailed::ParamType(failed)) => {
                    let reason = match failed {
                        VerifyObjWellDefinedResult::Failed { reason, .. } => reason,
                        _ => fail_to_verify_obj_well_defined_others(
                            "forall: typed parameter well-definedness failed".to_string(),
                        ),
                    };
                    return Ok(ForallLocalOutcome::FailWd(
                        FailToVerifyForallFactWellDefinedResult::ParamType(reason),
                    ));
                }
                Err(IntroduceTypedParametersFailed::AutoOpenStructLayer { failed, .. }) => {
                    return Ok(ForallLocalOutcome::FailWd(
                        FailToVerifyForallFactWellDefinedResult::AutoOpenStructLayer(failed),
                    ));
                }
            };

        let mut assumed_dom_facts = Vec::with_capacity(fact.dom_facts.len());
        for (failed_index, dom) in fact.dom_facts.iter().enumerate() {
            match self.assume_dom_fact(dom, verify_state.clone())? {
                Ok(assumed) => {
                    assumed_dom_facts.push(assumed);
                }
                Err(failed_dom) => {
                    return Ok(ForallLocalOutcome::FailWd(
                        FailToVerifyForallFactWellDefinedResult::DomFact {
                            failed_index,
                            param_type_well_defined: introduced_params.param_type_well_defined,
                            succeeded_dom: assumed_dom_facts
                                .into_iter()
                                .map(|a| a.well_defined)
                                .collect(),
                            failed_dom: Box::new(failed_dom),
                        },
                    ));
                }
            }
        }

        let mut proved_then_facts = Vec::with_capacity(fact.then_facts.len());
        for (failed_then_index, then) in fact.then_facts.iter().enumerate() {
            let then_fact: crate::ast::fact::Fact = then.clone().into();
            let verify_result = self.verify_fact(&then_fact, verify_state.clone())?;
            if verify_result.is_failed() {
                return Ok(ForallLocalOutcome::FailThen {
                    introduced_params,
                    assumed_dom_facts,
                    proved_then_facts,
                    failed_then_index,
                    failed_then: verify_result,
                });
            }
            let store_and_infer = self.store_fact_and_infer(&then_fact, verify_state)?;
            proved_then_facts.push(ProveAndStoreThenFactResult {
                verify_result,
                store_and_infer,
            });
        }

        Ok(ForallLocalOutcome::Success {
            introduced_params,
            assumed_dom_facts,
            proved_then_facts,
        })
    }

    fn assume_dom_fact(
        &mut self,
        dom: &crate::ast::fact::Fact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<AssumeDomFactResult, crate::execute::execute_fact_stmt::well_defined_results::FailToVerifyFactWellDefinedResult>,
    >{
        let well_defined = match self.verify_fact_well_definedness(dom, verify_state)? {
            VerifyFactWellDefinedResult::Success(proof) => proof,
            VerifyFactWellDefinedResult::Failed(reason) => {
                return Ok(Err(reason));
            }
        };
        let store_and_infer: StoreFactAndInferResult =
            self.store_fact_and_infer(dom, verify_state)?;
        Ok(Ok(AssumeDomFactResult {
            well_defined,
            store_and_infer,
        }))
    }
}

// Exact free identities and polarity remain significant. The existing exist
// alpha key handles its own witness binders after outer parameters are renamed.
fn same_quantified_source_fact(source: &Fact, goal: &Fact) -> bool {
    if std::mem::discriminant(source) != std::mem::discriminant(goal) {
        return false;
    }
    match (
        crate::ast::fact::exist_shaped_fact_from_fact(source),
        crate::ast::fact::exist_shaped_fact_from_fact(goal),
    ) {
        (Some(a), Some(b)) => {
            // Nested function/set binders also permit alpha-renaming. Keep
            // free identities, carriers and the complete existential body exact.
            crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::plain_exist_facts_alpha_equal(
                crate::exec_env::exist_shaped_fact_index_key::plain_exist_fact(&a),
                crate::exec_env::exist_shaped_fact_index_key::plain_exist_fact(&b),
            )
        }
        _ => source.ir() == goal.ir() || quantifier_free_source_facts_alpha_equal(source, goal),
    }
}

#[cfg(test)]
#[path = "../../../../tests/unit/execute/forall_source_replay/tests.rs"]
mod source_replay_tests;
