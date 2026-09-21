use crate::new_pipeline::ast::fact::ForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact::result::{
    forall_fact_result_from_success, forall_fact_result_from_then_fail,
    forall_fact_result_from_wd_fail,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact::FailToVerifyForallFactWellDefinedResult;
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact::{
    AssumeDomFactResult, ProveAndStoreThenFactResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::fail_to_verify_obj_well_defined_others;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyFactWellDefinedResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::execute::introduce_typed_parameters::{
    IntroduceTypedParametersFailed, IntroduceTypedParametersResult,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

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
                        VerifyObjWellDefinedResult::Failed(reason) => reason,
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
            let then_fact: crate::new_pipeline::ast::fact::Fact = then.clone().into();
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
            let store_and_infer = self.store_fact_and_infer(&then_fact)?;
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
        dom: &crate::new_pipeline::ast::fact::Fact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<AssumeDomFactResult, crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::FailToVerifyFactWellDefinedResult>,
    >{
        let well_defined = match self.verify_fact_well_definedness(dom, verify_state)? {
            VerifyFactWellDefinedResult::Success(proof) => proof,
            VerifyFactWellDefinedResult::Failed(reason) => {
                return Ok(Err(reason));
            }
        };
        let store_and_infer: StoreFactAndInferResult = self.store_fact_and_infer(dom)?;
        Ok(Ok(AssumeDomFactResult {
            well_defined,
            store_and_infer,
        }))
    }
}
