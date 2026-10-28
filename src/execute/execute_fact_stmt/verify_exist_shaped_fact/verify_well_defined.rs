use super::DetailedExistShapedFactWellDefinedProof;
use crate::ast::fact::{ExistShapedFact, PlainExistFact, QuantifierFreeFact};
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::well_defined_result::{
    ExistShapedFactWellDefinedProof, FailToVerifyExistShapedFactWellDefinedResult,
    VerifyExistShapedFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::verify_forall_fact::AssumeDomFactResult;
use crate::execute::execute_fact_stmt::well_defined_results::{
    fail_to_verify_obj_well_defined_others, FailToVerifyObjWellDefinedResult,
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::execute::IntroduceTypedParametersResult;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::result_detail::OutputDetail;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Shared by plain exist / exist! / not exist (same PlainExistFact payload).
    pub fn verify_exist_shaped_fact_well_definedness(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyExistShapedFactWellDefinedResult> {
        let (stages, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_plain_exist_fact_well_definedness_in_local(fact, verify_state.clone())
        })?;
        match stages {
            Ok((introduced_params, assumed_body_facts)) => {
                Ok(VerifyExistShapedFactWellDefinedResult::Success(
                    ExistShapedFactWellDefinedProof::new(self.result_detail(), || {
                        DetailedExistShapedFactWellDefinedProof {
                            introduced_params,
                            assumed_body_facts,
                            local_env,
                        }
                    }),
                ))
            }
            Err(reason) => Ok(VerifyExistShapedFactWellDefinedResult::Failed(reason)),
        }
    }

    fn verify_plain_exist_fact_well_definedness_in_local(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (IntroduceTypedParametersResult, Vec<AssumeDomFactResult>),
            FailToVerifyExistShapedFactWellDefinedResult,
        >,
    > {
        let plain = plain_exist_body(fact);
        let introduced_params = match self
            .verify_and_define_wd_parameters(&plain.typed_parameters, verify_state.clone())?
        {
            Ok(introduced) => introduced,
            Err(failed) => {
                return Ok(Err(
                    FailToVerifyExistShapedFactWellDefinedResult::ParamType {
                        fact: fact.clone(),
                        reason: extract_obj_wd_fail(failed),
                    },
                ));
            }
        };

        let mut assumed_body_facts = if self.result_detail() == OutputDetail::Detailed {
            Vec::with_capacity(plain.facts.len())
        } else {
            Vec::new()
        };
        for (failed_index, qf) in plain.facts.iter().enumerate() {
            match self.verify_quantifier_free_fact_well_definedness(qf, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    // Assume each body fact before later ones (same as forall dom
                    // and prop body): e.g. `a != 0 or b != 0` before `l = line(a,b,c)`.
                    let as_fact = quantifier_free_fact_to_fact(qf.clone());
                    let store_and_infer = self.store_fact_and_infer(&as_fact, verify_state)?;
                    proof.require_detail(self.result_detail(), "quantified WD assumption")?;
                    if self.result_detail() == OutputDetail::Detailed {
                        assumed_body_facts.push(AssumeDomFactResult {
                            well_defined: proof,
                            store_and_infer,
                        });
                    }
                }
                VerifyFactWellDefinedResult::Failed(failed_body) => {
                    return Ok(Err(
                        FailToVerifyExistShapedFactWellDefinedResult::BodyFact {
                            fact: fact.clone(),
                            failed_index,
                            param_type_well_defined: if self.result_detail()
                                == OutputDetail::Detailed
                            {
                                introduced_params.param_type_well_defined
                            } else {
                                Vec::new()
                            },
                            succeeded_body: assumed_body_facts
                                .into_iter()
                                .map(|a| a.well_defined)
                                .collect(),
                            failed_body: Box::new(failed_body),
                        },
                    ));
                }
            }
        }

        Ok(Ok((introduced_params, assumed_body_facts)))
    }
}

impl Runtime {
    // QuantifierFreeFact is only atomic / and / chain / or — call the matching WD entry.
    fn verify_quantifier_free_fact_well_definedness(
        &mut self,
        fact: &QuantifierFreeFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactWellDefinedResult> {
        match fact {
            QuantifierFreeFact::AtomicFact(atomic) => {
                self.wrap_atomic_fact_wd(atomic, verify_state)
            }
            QuantifierFreeFact::AndFact(and_fact) => self.wrap_and_fact_wd(and_fact, verify_state),
            QuantifierFreeFact::ChainFact(chain_fact) => {
                self.wrap_chain_fact_wd(chain_fact, verify_state)
            }
            QuantifierFreeFact::OrFact(or_fact) => self.wrap_or_fact_wd(or_fact, verify_state),
        }
    }
}

fn plain_exist_body(fact: &ExistShapedFact) -> &PlainExistFact {
    fact.plain()
}

fn extract_obj_wd_fail(failed: VerifyObjWellDefinedResult) -> FailToVerifyObjWellDefinedResult {
    match failed {
        VerifyObjWellDefinedResult::Failed { reason, .. } => reason,
        _ => {
            fail_to_verify_obj_well_defined_others("param type well-definedness failed".to_string())
        }
    }
}
