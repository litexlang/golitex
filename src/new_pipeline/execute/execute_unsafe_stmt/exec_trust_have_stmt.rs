//! `trust have` statement: WD param types and body facts, then bind and store.

use super::exec_trust_stmt::trust_verify_state;
use crate::new_pipeline::ast::stmt::TrustHaveStmt;
use crate::new_pipeline::exec_env::DefinedIdentifierInfo;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyWellDefinedResult, ParamTypeWellDefinedProof,
    StoreFactAndInferResult, VerifyFactResult, VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

pub enum ExecTrustHaveStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    BodyFactWellDefined(VerifyFactResult),
}

pub struct ExecTrustHaveStmtSuccessResult {
    pub statement: TrustHaveStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub body_facts_well_defined: Vec<FactWellDefinedProof>,
    pub defined_param_store_and_infer: StoreHaveObjAndInferResult,
    pub body_store_and_infer_results: Vec<StoreFactAndInferResult>,
}

pub enum ExecTrustHaveStmtResult {
    Success(ExecTrustHaveStmtSuccessResult),
    Failed(ExecTrustHaveStmtFailed),
}

impl ExecTrustHaveStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    pub(in crate::new_pipeline::execute) fn exec_trust_have_stmt(
        &mut self,
        stmt: &TrustHaveStmt,
    ) -> RuntimeResult<ExecTrustHaveStmtResult> {
        let verify_state = trust_verify_state();

        let param_type_well_defined =
            self.verify_typed_parameters_well_definedness(&stmt.param_def, verify_state.clone())?;
        let mut kept_param_type_well_defined = Vec::with_capacity(param_type_well_defined.len());
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
                return Ok(ExecTrustHaveStmtResult::Failed(
                    ExecTrustHaveStmtFailed::ParamType(failed),
                ));
            }
            kept_param_type_well_defined.push(proof);
        }
        let param_type_well_defined = kept_param_type_well_defined;

        let mut body_facts_well_defined = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            let wd = self.verify_fact_well_definedness(fact, verify_state.clone())?;
            if wd.is_failed() {
                return Ok(ExecTrustHaveStmtResult::Failed(
                    ExecTrustHaveStmtFailed::BodyFactWellDefined(
                        VerifyFactResult::FailToVerifyWellDefined,
                    ),
                ));
            }
            body_facts_well_defined.push(wd);
        }

        let defined_param_store_and_infer = self.define_trust_have_params(stmt)?;

        let mut body_store_and_infer_results = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            body_store_and_infer_results.push(self.store_fact_and_infer(fact)?);
        }

        Ok(ExecTrustHaveStmtResult::Success(
            ExecTrustHaveStmtSuccessResult {
                statement: stmt.clone(),
                param_type_well_defined,
                body_facts_well_defined,
                defined_param_store_and_infer,
                body_store_and_infer_results,
            },
        ))
    }

    fn define_trust_have_params(
        &mut self,
        stmt: &TrustHaveStmt,
    ) -> RuntimeResult<StoreHaveObjAndInferResult> {
        let mut stored_fact_ids = Vec::new();
        for group in &stmt.param_def.groups {
            for identifier in &group.params {
                if self.identifier_defined_in_stack(&identifier.name) {
                    return Err(RuntimeError::Invariant(format!(
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
                stored_fact_ids.push(self.ids.allocate_fact_id());
            }
        }
        Ok(StoreHaveObjAndInferResult { stored_fact_ids })
    }
}
