use crate::new_pipeline::ast::fact::ForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::{
    AssumeDomFactResult, ProveAndStoreThenFactResult, VerifyFactResult, VerifyForallFactResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::execute::introduce_typed_parameters::IntroduceTypedParametersResult;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::StoreFactAndInferResult;

impl Runtime {
    // Prove forall by local introduction:
    //   introduce typed params → assume dom → prove+store each then → take local_env.
    // Soft miss → FailToVerifyWellDefined / FailToSearchProof (no whole-forall store).
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
            Ok((introduced_params, assumed_dom_facts, proved_then_facts)) => {
                Ok(VerifyFactResult::ForallFact(Box::new(VerifyForallFactResult {
                    fact: fact.clone(),
                    introduced_params,
                    assumed_dom_facts,
                    proved_then_facts,
                    local_env,
                })))
            }
            Err(failed) => Ok(failed),
        }
    }

    fn verify_forall_fact_in_local(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (
                IntroduceTypedParametersResult,
                Vec<AssumeDomFactResult>,
                Vec<ProveAndStoreThenFactResult>,
            ),
            VerifyFactResult,
        >,
    > {
        let introduced_params =
            match self.introduce_typed_parameters(&fact.typed_parameters, verify_state.clone())? {
                Ok(result) => result,
                Err(_) => return Ok(Err(VerifyFactResult::FailToVerifyWellDefined)),
            };

        let mut assumed_dom_facts = Vec::with_capacity(fact.dom_facts.len());
        for dom in &fact.dom_facts {
            match self.assume_dom_fact(dom, verify_state.clone())? {
                Ok(assumed) => assumed_dom_facts.push(assumed),
                Err(failed) => return Ok(Err(failed)),
            }
        }

        let mut proved_then_facts = Vec::with_capacity(fact.then_facts.len());
        for then in &fact.then_facts {
            let then_fact: crate::new_pipeline::ast::fact::Fact = then.clone().into();
            let verify_result = self.verify_fact(&then_fact, verify_state.clone())?;
            if verify_result.is_failed() {
                return Ok(Err(verify_result));
            }
            let store_and_infer = self.store_fact_and_infer(&then_fact)?;
            proved_then_facts.push(ProveAndStoreThenFactResult {
                verify_result,
                store_and_infer,
            });
        }

        Ok(Ok((
            introduced_params,
            assumed_dom_facts,
            proved_then_facts,
        )))
    }

    fn assume_dom_fact(
        &mut self,
        dom: &crate::new_pipeline::ast::fact::Fact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<AssumeDomFactResult, VerifyFactResult>> {
        let well_defined = self.verify_fact_well_definedness(dom, verify_state)?;
        if well_defined.is_failed() {
            return Ok(Err(VerifyFactResult::FailToVerifyWellDefined));
        }
        let store_and_infer: StoreFactAndInferResult = self.store_fact_and_infer(dom)?;
        Ok(Ok(AssumeDomFactResult {
            well_defined,
            store_and_infer,
        }))
    }
}
