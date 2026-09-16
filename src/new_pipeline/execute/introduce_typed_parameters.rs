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

use crate::new_pipeline::ast::param::TypedParameterList;
use crate::new_pipeline::exec_env::DefinedIdentifierInfo;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FailToVerifyWellDefinedResult, ParamTypeWellDefinedProof, VerifyObjWellDefinedResult,
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
                    _ => VerifyObjWellDefinedResult::FailToVerifyWellDefined(
                        FailToVerifyWellDefinedResult::Others(
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

    // Stage 2: bind each identifier in the current top ExecEnv and record
    // type-fact ids. Type facts themselves still need KnownFactMemory wiring.
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
                        identifier: identifier.clone(),
                    },
                );
                // Type facts belong in KnownFactMemory once that store is wired.
                stored_fact_ids.push(self.ids.allocate_fact_id());
            }
        }
        Ok(StoreHaveObjAndInferResult { stored_fact_ids })
    }
}
