use crate::ast::fact::{ExistShapedFact, PlainExistFact, QuantifierFreeFact};
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::verify_exist_shaped_fact::well_defined_result::{
    ExistShapedFactWellDefinedProof, FailToVerifyExistShapedFactWellDefinedResult,
    VerifyExistShapedFactWellDefinedResult,
};
use crate::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, fail_to_verify_obj_well_defined_others, FailToVerifyObjWellDefinedResult, VerifyFactWellDefinedResult,
    VerifyObjWellDefinedResult,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Shared by plain exist / exist! / not exist (same PlainExistFact payload).
    pub fn verify_exist_shaped_fact_well_definedness(
        &mut self,
        fact: &ExistShapedFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyExistShapedFactWellDefinedResult> {
        let plain = plain_exist_body(fact);
        let (stages, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_plain_exist_fact_well_definedness_in_local(plain, verify_state.clone())
        })?;
        match stages {
            Ok((param_type_well_defined, body)) => Ok(VerifyExistShapedFactWellDefinedResult::Success(
                ExistShapedFactWellDefinedProof {
                    param_type_well_defined,
                    body,
                    local_env,
                },
            )),
            Err(reason) => Ok(VerifyExistShapedFactWellDefinedResult::Failed(reason)),
        }
    }

    fn verify_plain_exist_fact_well_definedness_in_local(
        &mut self,
        plain: &PlainExistFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (Vec<ParamTypeWellDefinedProof>, Vec<FactWellDefinedProof>),
            FailToVerifyExistShapedFactWellDefinedResult,
        >,
    > {
        let param_type_well_defined = match self.verify_and_define_wd_parameters(
            &plain.typed_parameters,
            verify_state.clone(),
        )? {
            Ok(proofs) => proofs,
            Err(failed) => {
                return Ok(Err(FailToVerifyExistShapedFactWellDefinedResult::ParamType(
                    extract_obj_wd_fail(failed),
                )));
            }
        };

        let mut succeeded_body = Vec::with_capacity(plain.facts.len());
        for (failed_index, qf) in plain.facts.iter().enumerate() {
            match self.verify_quantifier_free_fact_well_definedness(qf, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    // Assume each body fact before later ones (same as forall dom
                    // and prop body): e.g. `a != 0 or b != 0` before `l = line(a,b,c)`.
                    let as_fact = quantifier_free_fact_to_fact(qf.clone());
                    let _ = self.store_fact_and_infer(&as_fact)?;
                    succeeded_body.push(proof);
                }
                VerifyFactWellDefinedResult::Failed(failed_body) => {
                    return Ok(Err(FailToVerifyExistShapedFactWellDefinedResult::BodyFact {
                        failed_index,
                        param_type_well_defined,
                        succeeded_body,
                        failed_body: Box::new(failed_body),
                    }));
                }
            }
        }

        Ok(Ok((param_type_well_defined, succeeded_body)))
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
        _ => fail_to_verify_obj_well_defined_others(
            "param type well-definedness failed".to_string(),
        ),
    }
}
