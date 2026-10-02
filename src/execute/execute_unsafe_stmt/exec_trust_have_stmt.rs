//! `trust have` statement: WD param types, define, then WD + store body facts.
//!
//! Example:
//!   trust have denominator R:
//!       denominator != 0
//!   # then `1 / denominator` is well-defined

use super::exec_trust_stmt::trust_verify_state;
use crate::ast::obj::Obj;
use crate::ast::stmt::TrustHaveStmt;
use crate::execute::execute_fact_stmt::{
    FactWellDefinedProof, FailToVerifyFactWellDefinedResult, ParamTypeWellDefinedProof,
    StoreFactAndInferResult, VerifyFactWellDefinedResult, VerifyObjWellDefinedResult,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::execute::introduce_typed_parameters::SharedHaveDefinition;
use crate::execute::IntroduceTypedParametersFailed;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;
use std::rc::Rc;

pub enum ExecTrustHaveStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
    BodyFactWellDefined(FailToVerifyFactWellDefinedResult),
}

// Pipeline: param-type WD → define → auto-open → body WD → body store.
pub struct ExecTrustHaveStmtSuccessResult {
    pub statement: TrustHaveStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub defined_param_store_and_infer: StoreHaveObjAndInferResult,
    pub auto_opened_struct_layers:
        Option<Vec<crate::execute::ReleaseOneStructLayerProof>>,
    pub body_facts_well_defined: Vec<FactWellDefinedProof>,
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
    // Body facts may mention the new names, so define (and auto-open) first;
    // soft Fail still discards the temp ExecEnv opened by exec_stmt.
    // Body facts are rewritten to file-root mentions before WD/store so later
    // free refs (`WithExportFileId`) match the known facts.
    pub(in crate::execute) fn exec_trust_have_stmt(
        &mut self,
        stmt: &TrustHaveStmt,
    ) -> RuntimeResult<ExecTrustHaveStmtResult> {
        let verify_state = trust_verify_state();

        let introduced = match self.introduce_typed_parameters_with_definition(
            &stmt.param_def, verify_state.clone(),
            Some(SharedHaveDefinition::TrustHave(Rc::new(stmt.clone()))),
        )? {
            Ok(result) => result,
            Err(IntroduceTypedParametersFailed::ParamType(failed)) => {
                return Ok(ExecTrustHaveStmtResult::Failed(
                    ExecTrustHaveStmtFailed::ParamType(failed),
                ));
            }
            Err(IntroduceTypedParametersFailed::AutoOpenStructLayer { failed, .. }) => {
                return Ok(ExecTrustHaveStmtResult::Failed(
                    ExecTrustHaveStmtFailed::AutoOpenStructLayer(failed),
                ));
            }
        };
        let param_type_well_defined = introduced.param_type_well_defined;
        let defined_param_store_and_infer = introduced.defined_params;
        let auto_opened_struct_layers = introduced.auto_opened_struct_layers;

        let subst = file_root_subst_for_trust_have_params(self, &stmt.param_def);
        let mut rewritten_body = Vec::with_capacity(stmt.facts.len());
        for fact in &stmt.facts {
            match self.inst_fact(fact, &subst) {
                Ok(inst) => rewritten_body.push(inst),
                Err(e) => {
                    return Err(crate::runtime::RuntimeError::InternalBug(
                        format!("trust have body instantiate: {e}"),
                    ));
                }
            }
        }

        let mut body_facts_well_defined = Vec::with_capacity(rewritten_body.len());
        for fact in &rewritten_body {
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

        let mut body_store_and_infer_results = Vec::with_capacity(rewritten_body.len());
        for fact in &rewritten_body {
            body_store_and_infer_results.push(self.store_fact_and_infer(fact)?);
        }

        Ok(ExecTrustHaveStmtResult::Success(
            ExecTrustHaveStmtSuccessResult {
                statement: stmt.clone(),
                param_type_well_defined,
                defined_param_store_and_infer,
                auto_opened_struct_layers,
                body_facts_well_defined,
                body_store_and_infer_results,
            },
        ))
    }
}

fn file_root_subst_for_trust_have_params(
    runtime: &Runtime,
    param_def: &crate::ast::param::TypedParameterList,
) -> HashMap<IdentifierId, Obj> {
    let mut subst = HashMap::new();
    for group in &param_def.groups {
        for param in &group.params {
            subst.insert(
                param.id,
                Obj::Identifier(runtime.identifier_obj_for_stored_mention(param)),
            );
        }
    }
    subst
}
