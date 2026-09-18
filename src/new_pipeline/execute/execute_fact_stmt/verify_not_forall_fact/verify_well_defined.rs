use crate::new_pipeline::ast::fact::{Fact, NotForallFact, QuantifierFreeFact};
use crate::new_pipeline::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_not_forall_fact::well_defined_result::{
    FailToVerifyNotForallFactWellDefinedResult, NotForallFactWellDefinedProof,
    VerifyNotForallFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, fail_to_verify_obj_well_defined_others, FailToVerifyObjWellDefinedResult, VerifyFactWellDefinedResult,
    VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

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
            Ok((param_type_well_defined, dom, then)) => {
                Ok(VerifyNotForallFactWellDefinedResult::Success(
                    NotForallFactWellDefinedProof {
                        param_type_well_defined,
                        dom,
                        then,
                        local_env,
                    },
                ))
            }
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
                Vec<ParamTypeWellDefinedProof>,
                Vec<FactWellDefinedProof>,
                Vec<FactWellDefinedProof>,
            ),
            FailToVerifyNotForallFactWellDefinedResult,
        >,
    > {
        let param_type_well_defined = match self.verify_typed_parameters_well_definedness_or_fail(
            &fact.typed_parameters,
            verify_state.clone(),
        )? {
            Ok(proofs) => proofs,
            Err(failed) => {
                return Ok(Err(FailToVerifyNotForallFactWellDefinedResult::ParamType(
                    extract_obj_wd_fail(failed),
                )));
            }
        };

        self.define_typed_parameters_in_current_env(&fact.typed_parameters)?;

        let mut succeeded_dom = Vec::with_capacity(fact.dom_facts.len());
        for (failed_index, dom) in fact.dom_facts.iter().enumerate() {
            match self.verify_quantifier_free_as_fact_wd(dom, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => succeeded_dom.push(proof),
                VerifyFactWellDefinedResult::Failed(failed_dom) => {
                    return Ok(Err(FailToVerifyNotForallFactWellDefinedResult::DomFact {
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
            match self.verify_quantifier_free_as_fact_wd(then, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => succeeded_then.push(proof),
                VerifyFactWellDefinedResult::Failed(failed_then) => {
                    return Ok(Err(FailToVerifyNotForallFactWellDefinedResult::ThenFact {
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
        VerifyObjWellDefinedResult::Failed(reason) => reason,
        _ => fail_to_verify_obj_well_defined_others(
            "param type well-definedness failed".to_string(),
        ),
    }
}
