//! `trust have` statement: WD param types and body facts, then bind and store.

use super::exec_trust_stmt::trust_verify_state;
use crate::new_pipeline::ast::stmt::TrustHaveStmt;
use crate::new_pipeline::exec_env::StoredIdentifierDefinition;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, ParamTypeWellDefinedProof,
    StoreFactAndInferResult, VerifyFactWellDefinedResult, VerifyObjWellDefinedResult,
};
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::rc::Rc;

pub enum ExecTrustHaveStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    BodyFactWellDefined(FailToVerifyFactWellDefinedResult),
    AutoOpenStructLayer(crate::new_pipeline::execute::FailToReleaseOneStructLayer),
}

pub struct ExecTrustHaveStmtSuccessResult {
    pub statement: TrustHaveStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub body_facts_well_defined: Vec<FactWellDefinedProof>,
    pub defined_param_store_and_infer: StoreHaveObjAndInferResult,
    pub auto_opened_struct_layers:
        Option<Vec<crate::new_pipeline::execute::ReleaseOneStructLayerProof>>,
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
    // Body WD currently runs before define (legacy order). Params use the
    // shared WD + define helpers, split around that body stage.
    pub(in crate::new_pipeline::execute) fn exec_trust_have_stmt(
        &mut self,
        stmt: &TrustHaveStmt,
    ) -> RuntimeResult<ExecTrustHaveStmtResult> {
        let verify_state = trust_verify_state();

        let param_type_well_defined = match self
            .verify_typed_parameters_well_definedness_or_fail(&stmt.param_def, verify_state.clone())?
        {
            Ok(proofs) => proofs,
            Err(failed) => {
                return Ok(ExecTrustHaveStmtResult::Failed(
                    ExecTrustHaveStmtFailed::ParamType(failed),
                ));
            }
        };

        let mut body_facts_well_defined = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            match self.verify_fact_well_definedness(fact, verify_state.clone())? {
                VerifyFactWellDefinedResult::Success(proof) => {
                    body_facts_well_defined.push(proof);
                }
                VerifyFactWellDefinedResult::Failed(reason) => {
                    return Ok(ExecTrustHaveStmtResult::Failed(
                        ExecTrustHaveStmtFailed::BodyFactWellDefined(reason),
                    ));
                }
            }
        }

        let defined_param_store_and_infer = self.define_typed_parameters_in_current_env(
            &stmt.param_def,
            Some(StoredIdentifierDefinition::TrustHave(Rc::new(stmt.clone()))),
        )?;

        let auto_opened_struct_layers =
            match self.auto_open_struct_layers_for_typed_parameters(&stmt.param_def)? {
                Ok(layers) => layers,
                Err((_, failed)) => {
                    return Ok(ExecTrustHaveStmtResult::Failed(
                        ExecTrustHaveStmtFailed::AutoOpenStructLayer(failed),
                    ));
                }
            };

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
                auto_opened_struct_layers,
                body_store_and_infer_results,
            },
        ))
    }
}
