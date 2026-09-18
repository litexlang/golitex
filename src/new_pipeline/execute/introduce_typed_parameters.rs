//! Introduce typed parameters into the current top ExecEnv.
//!
//! Shared by `have` / `trust have` / `prop` / `forall` / … whenever a
//! `TypedParameterList` must become live identifiers with type facts.
//!
//! Pipeline (field order matches):
//! 1. param-type WD
//! 2. define identifiers + store type-membership facts
//!
//! Callers that insert extra stages between WD and define (e.g. `have`'s
//! nonempty checks) should call the two stages separately:
//! `verify_typed_parameters_well_definedness` then
//! `define_typed_parameters_in_current_env`.

use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::exec_env::DefinedIdentifierInfo;
use crate::new_pipeline::execute::execute_fact_stmt::{
    fail_to_verify_obj_well_defined_others, ParamTypeWellDefinedProof, VerifyObjWellDefinedResult,
    VerifyState,
};
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

// Stage-ordered evidence for introducing a TypedParameterList.
pub struct IntroduceTypedParametersResult {
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub defined_params: StoreHaveObjAndInferResult,
}

impl Runtime {
    // WD param types, then define params into the current top ExecEnv.
    // Soft miss: Ok(Err(wd)); operational / internal bug: Err(...).
    pub fn introduce_typed_parameters(
        &mut self,
        typed_parameters: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<IntroduceTypedParametersResult, VerifyObjWellDefinedResult>> {
        let param_type_well_defined = match self
            .verify_typed_parameters_well_definedness_or_fail(typed_parameters, verify_state)?
        {
            Ok(proofs) => proofs,
            Err(failed) => return Ok(Err(failed)),
        };

        let defined_params = self.define_typed_parameters_in_current_env(typed_parameters)?;

        Ok(Ok(IntroduceTypedParametersResult {
            param_type_well_defined,
            defined_params,
        }))
    }

    // Stage 1 only: soft-fail when any ParamType WD fails.
    pub fn verify_typed_parameters_well_definedness_or_fail(
        &mut self,
        typed_parameters: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<Vec<ParamTypeWellDefinedProof>, VerifyObjWellDefinedResult>> {
        let param_type_well_defined =
            self.verify_typed_parameters_well_definedness(typed_parameters, verify_state)?;
        let mut kept = Vec::with_capacity(param_type_well_defined.len());
        for proof in param_type_well_defined {
            if proof.is_failed() {
                let failed = match proof {
                    ParamTypeWellDefinedProof::Obj(wd) => wd,
                    _ => VerifyObjWellDefinedResult::Failed(
                        fail_to_verify_obj_well_defined_others(
                            "param type well-definedness failed".to_string(),
                        ),
                    ),
                };
                return Ok(Err(failed));
            }
            kept.push(proof);
        }
        Ok(Ok(kept))
    }

    // Stage 2: bind each identifier and store its type fact into KnownFactMemory.
    // Example: `have x R` stores `x $in R`.
    pub fn define_typed_parameters_in_current_env(
        &mut self,
        typed_parameters: &TypedParameterList,
    ) -> RuntimeResult<StoreHaveObjAndInferResult> {
        let mut stored_fact_ids = Vec::new();
        for group in &typed_parameters.groups {
            for identifier in &group.params {
                if self.identifier_defined_in_stack(&identifier.name) {
                    return Err(RuntimeError::InternalBug(format!(
                        "identifier `{}` is already defined in this ExecEnv",
                        identifier.name
                    )));
                }
                self.top_exec_env_mut().definitions.identifiers.insert(
                    identifier.name.clone(),
                    DefinedIdentifierInfo {
                        identifier: identifier.name.clone(),
                    },
                );
                // Env key is plain; type-fact mention qualifies at file root.
                let element = Obj::Identifier(self.identifier_obj_for_stored_mention(identifier));
                let type_fact = match &group.param_type {
                    ParamType::Obj(param_set) => Fact::AtomicFact(AtomicFact::InFact(InFact {
                        fact_id: self.ids.allocate_fact_id(),
                        element,
                        set: param_set.clone(),
                        line_file: None,
                    })),
                    ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
                        fact_id: self.ids.allocate_fact_id(),
                        set: element,
                        line_file: None,
                    })),
                    ParamType::NonemptySet(_) => {
                        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                            fact_id: self.ids.allocate_fact_id(),
                            set: element,
                            line_file: None,
                        }))
                    }
                    ParamType::FiniteSet(_) => {
                        Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
                            fact_id: self.ids.allocate_fact_id(),
                            set: element,
                            line_file: None,
                        }))
                    }
                };
                let store_result = self.store_fact_and_infer(&type_fact)?;
                stored_fact_ids.extend(store_result.stored_fact_ids());
            }
        }
        Ok(StoreHaveObjAndInferResult { stored_fact_ids })
    }
}
