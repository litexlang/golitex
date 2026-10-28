use super::DetailedNotForallFactWellDefinedProof;
use crate::ast::fact::{Fact, NotForallFact, QuantifierFreeFact};
use crate::execute::execute_fact_stmt::verify_forall_fact::AssumeDomFactResult;
use crate::execute::execute_fact_stmt::verify_not_forall_fact::well_defined_result::{
    FailToVerifyNotForallFactWellDefinedResult, NotForallFactWellDefinedProof,
    VerifyNotForallFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::well_defined_results::{
    fail_to_verify_obj_well_defined_others, FactWellDefinedProof, FailToVerifyObjWellDefinedResult,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::execute::IntroduceTypedParametersResult;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::result_detail::OutputDetail;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // WD for `not forall`: same binder obligations as forall (params/dom/then),
    // without proving the counterexample exist.
    pub fn verify_not_forall_fact_well_definedness(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyNotForallFactWellDefinedResult> {
        let (stages, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_not_forall_fact_well_definedness_in_local(fact, verify_state.clone())
        })?;
        match stages {
            Ok((introduced_params, assumed_dom_facts, then)) => Ok(
                VerifyNotForallFactWellDefinedResult::Success(NotForallFactWellDefinedProof::new(
                    self.result_detail(),
                    || DetailedNotForallFactWellDefinedProof {
                        introduced_params,
                        assumed_dom_facts,
                        then,
                        local_env,
                    },
                )),
            ),
            Err(reason) => Ok(VerifyNotForallFactWellDefinedResult::Failed(reason)),
        }
    }

    fn verify_not_forall_fact_well_definedness_in_local(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (
                IntroduceTypedParametersResult,
                Vec<AssumeDomFactResult>,
                Vec<FactWellDefinedProof>,
            ),
            FailToVerifyNotForallFactWellDefinedResult,
        >,
    > {
        let introduced_params = match self
            .verify_and_define_wd_parameters(&fact.typed_parameters, verify_state.clone())?
        {
            Ok(introduced) => introduced,
            Err(failed) => {
                return Ok(Err(FailToVerifyNotForallFactWellDefinedResult::ParamType {
                    fact: fact.clone(),
                    reason: extract_obj_wd_fail(failed),
                }));
            }
        };

        let mut assumed_dom_facts = if self.result_detail() == OutputDetail::Detailed {
            Vec::with_capacity(fact.dom_facts.len())
        } else {
            Vec::new()
        };
        for (failed_index, dom) in fact.dom_facts.iter().enumerate() {
            match self.verify_quantifier_free_as_fact_wd(dom, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    // Checked antecedents guard later domains and conclusions.
                    // This binder environment is retained as evidence, not merged.
                    let store_and_infer = self.store_fact_and_infer(
                        &quantifier_free_fact_to_fact(dom.clone()),
                        verify_state,
                    )?;
                    proof.require_detail(self.result_detail(), "quantified WD assumption")?;
                    if self.result_detail() == OutputDetail::Detailed {
                        assumed_dom_facts.push(AssumeDomFactResult {
                            well_defined: proof,
                            store_and_infer,
                        });
                    }
                }
                VerifyFactWellDefinedResult::Failed(failed_dom) => {
                    return Ok(Err(FailToVerifyNotForallFactWellDefinedResult::DomFact {
                        fact: fact.clone(),
                        failed_index,
                        param_type_well_defined: if self.result_detail() == OutputDetail::Detailed {
                            introduced_params.param_type_well_defined
                        } else {
                            Vec::new()
                        },
                        succeeded_dom: assumed_dom_facts
                            .into_iter()
                            .map(|a| a.well_defined)
                            .collect(),
                        failed_dom: Box::new(failed_dom),
                    }));
                }
            }
        }

        let mut succeeded_then = if self.result_detail() == OutputDetail::Detailed {
            Vec::with_capacity(fact.then_facts.len())
        } else {
            Vec::new()
        };
        for (failed_index, then) in fact.then_facts.iter().enumerate() {
            match self.verify_quantifier_free_as_fact_wd(then, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    proof.require_detail(self.result_detail(), "quantified WD conclusion")?;
                    if self.result_detail() == OutputDetail::Detailed {
                        succeeded_then.push(proof);
                    }
                }
                VerifyFactWellDefinedResult::Failed(failed_then) => {
                    return Ok(Err(FailToVerifyNotForallFactWellDefinedResult::ThenFact {
                        fact: fact.clone(),
                        failed_index,
                        param_type_well_defined: if self.result_detail() == OutputDetail::Detailed {
                            introduced_params.param_type_well_defined
                        } else {
                            Vec::new()
                        },
                        succeeded_dom: assumed_dom_facts
                            .into_iter()
                            .map(|a| a.well_defined)
                            .collect(),
                        succeeded_then,
                        failed_then: Box::new(failed_then),
                    }));
                }
            }
        }

        Ok(Ok((introduced_params, assumed_dom_facts, succeeded_then)))
    }

    fn verify_quantifier_free_as_fact_wd(
        &mut self,
        fact: &QuantifierFreeFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        let as_fact: Fact = match fact {
            QuantifierFreeFact::AtomicFact(a) => a.clone().into(),
            QuantifierFreeFact::AndFact(a) => Fact::AndFact(a.clone()),
            QuantifierFreeFact::ChainFact(c) => Fact::ChainFact(c.clone()),
            QuantifierFreeFact::OrFact(o) => Fact::OrFact(o.clone()),
        };
        self.verify_fact_well_definedness(&as_fact, verify_state)
    }
}

fn extract_obj_wd_fail(failed: VerifyObjWellDefinedResult) -> FailToVerifyObjWellDefinedResult {
    match failed {
        VerifyObjWellDefinedResult::Failed { reason, .. } => reason,
        _ => {
            fail_to_verify_obj_well_defined_others("param type well-definedness failed".to_string())
        }
    }
}
