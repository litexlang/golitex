use crate::new_pipeline::ast::fact::{Fact, ForallFactWithIff};
use crate::new_pipeline::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact_with_iff::well_defined_result::{
    FailToVerifyForallFactWithIffWellDefinedResult, ForallFactWithIffWellDefinedProof,
    VerifyForallFactWithIffWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, fail_to_verify_obj_well_defined_others, FailToVerifyObjWellDefinedResult, VerifyFactWellDefinedResult,
    VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // WD for `forall … <=>:`: params, dom, then, and iff clauses in one local scope.
    // Soft miss example: ill-defined object inside an iff clause under `trust`.
    pub fn verify_forall_fact_with_iff_well_definedness(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyForallFactWithIffWellDefinedResult> {
        let (stages, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_forall_fact_with_iff_well_definedness_in_local(fact, verify_state.clone())
        })?;
        match stages {
            Ok((param_type_well_defined, dom, then, iff)) => {
                Ok(VerifyForallFactWithIffWellDefinedResult::Success(
                    ForallFactWithIffWellDefinedProof {
                        param_type_well_defined,
                        dom,
                        then,
                        iff,
                        local_env,
                    },
                ))
            }
            Err(reason) => Ok(VerifyForallFactWithIffWellDefinedResult::Failed(reason)),
        }
    }

    fn verify_forall_fact_with_iff_well_definedness_in_local(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (
                Vec<ParamTypeWellDefinedProof>,
                Vec<FactWellDefinedProof>,
                Vec<FactWellDefinedProof>,
                Vec<FactWellDefinedProof>,
            ),
            FailToVerifyForallFactWithIffWellDefinedResult,
        >,
    > {
        let inner = &fact.forall_fact;
        let param_type_well_defined = match self.verify_typed_parameters_well_definedness_or_fail(
            &inner.typed_parameters,
            verify_state.clone(),
        )? {
            Ok(proofs) => proofs,
            Err(failed) => {
                return Ok(Err(FailToVerifyForallFactWithIffWellDefinedResult::ParamType(
                    extract_obj_wd_fail(failed),
                )));
            }
        };

        self.define_typed_parameters_in_current_env(&inner.typed_parameters, None)?;

        let mut succeeded_dom = Vec::with_capacity(inner.dom_facts.len());
        for (failed_index, dom) in inner.dom_facts.iter().enumerate() {
            match self.verify_fact_well_definedness(dom, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => succeeded_dom.push(proof),
                VerifyFactWellDefinedResult::Failed(failed_dom) => {
                    return Ok(Err(FailToVerifyForallFactWithIffWellDefinedResult::DomFact {
                        failed_index,
                        param_type_well_defined,
                        succeeded_dom,
                        failed_dom: Box::new(failed_dom),
                    }));
                }
            }
        }

        let mut succeeded_then = Vec::with_capacity(inner.then_facts.len());
        for (failed_index, then) in inner.then_facts.iter().enumerate() {
            let then_fact: Fact = then.clone().into();
            match self.verify_fact_well_definedness(&then_fact, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => succeeded_then.push(proof),
                VerifyFactWellDefinedResult::Failed(failed_then) => {
                    return Ok(Err(FailToVerifyForallFactWithIffWellDefinedResult::ThenFact {
                        failed_index,
                        param_type_well_defined,
                        succeeded_dom,
                        succeeded_then,
                        failed_then: Box::new(failed_then),
                    }));
                }
            }
        }

        let mut succeeded_iff = Vec::with_capacity(fact.iff_facts.len());
        for (failed_index, iff) in fact.iff_facts.iter().enumerate() {
            let iff_fact: Fact = iff.clone().into();
            match self.verify_fact_well_definedness(&iff_fact, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => succeeded_iff.push(proof),
                VerifyFactWellDefinedResult::Failed(failed_iff) => {
                    return Ok(Err(FailToVerifyForallFactWithIffWellDefinedResult::IffFact {
                        failed_index,
                        param_type_well_defined,
                        succeeded_dom,
                        succeeded_then,
                        succeeded_iff,
                        failed_iff: Box::new(failed_iff),
                    }));
                }
            }
        }

        Ok(Ok((
            param_type_well_defined,
            succeeded_dom,
            succeeded_then,
            succeeded_iff,
        )))
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
