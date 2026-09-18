use crate::new_pipeline::ast::fact::{ExistFactFamily, PlainExistFact, QuantifierFreeFact};
use crate::new_pipeline::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_exist_fact::well_defined_result::{
    ExistFactWellDefinedProof, FailToVerifyExistFactWellDefinedResult,
    VerifyExistFactWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::well_defined_results::{
    FactWellDefinedProof, FailToVerifyObjWellDefinedResult, VerifyFactWellDefinedResult,
    VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Shared by plain exist / exist! / not exist (same PlainExistFact payload).
    pub fn verify_exist_fact_well_definedness(
        &mut self,
        fact: &ExistFactFamily,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyExistFactWellDefinedResult> {
        let plain = plain_exist_body(fact);
        let (stages, local_env) = self.run_in_local_env_and_take_env(|rt| {
            rt.verify_plain_exist_fact_well_definedness_in_local(plain, verify_state.clone())
        })?;
        match stages {
            Ok((param_type_well_defined, body)) => Ok(VerifyExistFactWellDefinedResult::Success(
                ExistFactWellDefinedProof {
                    param_type_well_defined,
                    body,
                    local_env,
                },
            )),
            Err(reason) => Ok(VerifyExistFactWellDefinedResult::Failed(reason)),
        }
    }

    fn verify_plain_exist_fact_well_definedness_in_local(
        &mut self,
        plain: &PlainExistFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Result<
            (Vec<ParamTypeWellDefinedProof>, Vec<FactWellDefinedProof>),
            FailToVerifyExistFactWellDefinedResult,
        >,
    > {
        let param_type_well_defined = match self.verify_typed_parameters_well_definedness_or_fail(
            &plain.typed_parameters,
            verify_state.clone(),
        )? {
            Ok(proofs) => proofs,
            Err(failed) => {
                return Ok(Err(FailToVerifyExistFactWellDefinedResult::ParamType(
                    extract_obj_wd_fail(failed),
                )));
            }
        };

        self.define_typed_parameters_in_current_env(&plain.typed_parameters)?;

        let mut succeeded_body = Vec::with_capacity(plain.facts.len());
        for (failed_index, qf) in plain.facts.iter().enumerate() {
            match self.verify_quantifier_free_fact_well_definedness(qf, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => succeeded_body.push(proof),
                VerifyFactWellDefinedResult::Failed(failed_body) => {
                    return Ok(Err(FailToVerifyExistFactWellDefinedResult::BodyFact {
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

fn plain_exist_body(fact: &ExistFactFamily) -> &PlainExistFact {
    match fact {
        ExistFactFamily::Exist(p)
        | ExistFactFamily::ExistUnique(p)
        | ExistFactFamily::NotExist(p) => p,
    }
}

fn extract_obj_wd_fail(failed: VerifyObjWellDefinedResult) -> FailToVerifyObjWellDefinedResult {
    match failed {
        VerifyObjWellDefinedResult::FailToVerifyWellDefined(reason) => reason,
        _ => FailToVerifyObjWellDefinedResult::Others(
            "param type well-definedness failed".to_string(),
        ),
    }
}
