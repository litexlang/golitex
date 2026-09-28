use crate::new_pipeline::ast::fact::{Fact, ForallFact};
use crate::new_pipeline::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact::well_defined_result::{
    FailToVerifyForallFactWellDefinedResult, ForallFactWellDefinedProof,
    VerifyForallFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, fail_to_verify_obj_well_defined_others, FailToVerifyObjWellDefinedResult, VerifyFactWellDefinedResult,
    VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Forall WD (for trust / nested dom / dispatcher): local binder scope,
    // param-type WD → each dom WD → each then WD. Does not prove then truth.
    // Example soft miss: `trust forall x R: 1 / 0 = x`.
    pub fn verify_forall_fact_well_definedness(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyForallFactWellDefinedResult> {
        let (stages, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_forall_fact_well_definedness_in_local(fact, verify_state.clone())
        })?;
        match stages {
            Ok((param_type_well_defined, dom, then)) => {
                Ok(VerifyForallFactWellDefinedResult::Success(
                    ForallFactWellDefinedProof {
                        param_type_well_defined,
                        dom,
                        then,
                        local_env,
                    },
                ))
            }
            Err(reason) => Ok(VerifyForallFactWellDefinedResult::Failed(reason)),
        }
    }

    fn verify_forall_fact_well_definedness_in_local(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (
                Vec<ParamTypeWellDefinedProof>,
                Vec<FactWellDefinedProof>,
                Vec<FactWellDefinedProof>,
            ),
            FailToVerifyForallFactWellDefinedResult,
        >,
    > {
        let param_type_well_defined = match self.verify_typed_parameters_well_definedness_or_fail(
            &fact.typed_parameters,
            verify_state.clone(),
        )? {
            Ok(proofs) => proofs,
            Err(failed) => {
                return Ok(Err(FailToVerifyForallFactWellDefinedResult::ParamType(
                    extract_obj_wd_fail(failed),
                )));
            }
        };

        self.define_typed_parameters_in_current_env(&fact.typed_parameters, None)?;

        let mut succeeded_dom = Vec::with_capacity(fact.dom_facts.len());
        for (failed_index, dom) in fact.dom_facts.iter().enumerate() {
            match self.verify_fact_well_definedness(dom, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    // Assume each dom before then-WD so domain-restricted
                    // applications (e.g. `f(x)` under `x > 0`) can pass.
                    let _ = self.store_fact_and_infer(dom)?;
                    succeeded_dom.push(proof);
                }
                VerifyFactWellDefinedResult::Failed(failed_dom) => {
                    return Ok(Err(FailToVerifyForallFactWellDefinedResult::DomFact {
                        failed_index,
                        param_type_well_defined,
                        succeeded_dom,
                        failed_dom: Box::new(failed_dom),
                    }));
                }
            }
        }

        let mut succeeded_then = Vec::with_capacity(fact.then_facts.len());
        for (failed_index, then) in fact.then_facts.iter().enumerate() {
            let then_fact: Fact = then.clone().into();
            match self.verify_fact_well_definedness(&then_fact, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => succeeded_then.push(proof),
                VerifyFactWellDefinedResult::Failed(failed_then) => {
                    return Ok(Err(FailToVerifyForallFactWellDefinedResult::ThenFact {
                        failed_index,
                        param_type_well_defined,
                        succeeded_dom,
                        succeeded_then,
                        failed_then: Box::new(failed_then),
                    }));
                }
            }
        }

        Ok(Ok((param_type_well_defined, succeeded_dom, succeeded_then)))
    }
}

fn extract_obj_wd_fail(failed: VerifyObjWellDefinedResult) -> FailToVerifyObjWellDefinedResult {
    match failed {
        VerifyObjWellDefinedResult::Failed { reason, .. } => reason,
        _ => fail_to_verify_obj_well_defined_others(
            "param type well-definedness failed".to_string(),
        ),
    }
}
