use crate::ast::fact::{AtomicFact, Fact, IsNonemptySetFact};
use crate::ast::obj::{Obj, FunctionSpace};
use crate::ast::param::{ParamType, TypedParameterList};
use crate::ast::stmt::HaveObjInNonemptySetOrParamTypeStmt;
use crate::execute::exec_stmt_result::{
    ParamTypeFactCheckResult, ParamTypeWellDefinedProof,
};
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::introduce_typed_parameters::SharedHaveDefinition;
use crate::runtime::{FactId, Runtime, RuntimeResult};
use std::rc::Rc;

pub struct StoreHaveObjAndInferResult {
    pub stored_fact_ids: Vec<FactId>,
}

pub enum ExecHaveObjInNonemptySetStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    NonemptyCheck(VerifyFactResult),
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
}

// Pipeline: WD param types → nonempty obligations → define symbols.
pub struct ExecHaveObjInNonemptySetStmtSuccessResult {
    pub statement: HaveObjInNonemptySetOrParamTypeStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub nonempty_checks: Vec<ParamTypeFactCheckResult>,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
    pub auto_opened_struct_layers:
        Option<Vec<crate::execute::ReleaseOneStructLayerProof>>,
}

pub enum ExecHaveObjInNonemptySetStmtResult {
    Success(ExecHaveObjInNonemptySetStmtSuccessResult),
    Failed(ExecHaveObjInNonemptySetStmtFailed),
}

impl ExecHaveObjInNonemptySetStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // `have x S` / `have A nonempty_set` / …
    // Nonempty checks sit between WD and define, so this does not call
    // `introduce_typed_parameters` as one shot.
    pub(super) fn exec_have_obj_in_nonempty_set_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> RuntimeResult<ExecHaveObjInNonemptySetStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
        };

        let param_type_well_defined = match self
            .verify_typed_parameters_well_definedness_or_fail(&stmt.param_def, verify_state.clone())?
        {
            Ok(proofs) => proofs,
            Err(failed) => {
                return Ok(ExecHaveObjInNonemptySetStmtResult::Failed(
                    ExecHaveObjInNonemptySetStmtFailed::ParamType(failed),
                ));
            }
        };

        let nonempty_checks =
            match self.verify_have_obj_nonempty_obligations(&stmt.param_def, verify_state)? {
                Ok(checks) => checks,
                Err(failed) => {
                    return Ok(ExecHaveObjInNonemptySetStmtResult::Failed(failed));
                }
            };

        let store_and_infer_result = self.define_typed_parameters_in_current_env(
            &stmt.param_def,
            Some(SharedHaveDefinition::HaveObjInNonemptySetOrParamType(Rc::new(
                stmt.clone(),
            ))),
        )?;

        let auto_opened_struct_layers =
            match self.auto_open_struct_layers_for_typed_parameters(&stmt.param_def)? {
                Ok(layers) => layers,
                Err((_, failed)) => {
                    return Ok(ExecHaveObjInNonemptySetStmtResult::Failed(
                        ExecHaveObjInNonemptySetStmtFailed::AutoOpenStructLayer(failed),
                    ));
                }
            };

        Ok(ExecHaveObjInNonemptySetStmtResult::Success(
            ExecHaveObjInNonemptySetStmtSuccessResult {
                statement: stmt.clone(),
                param_type_well_defined,
                nonempty_checks,
                store_and_infer_result,
                auto_opened_struct_layers,
            },
        ))
    }

    fn verify_have_obj_nonempty_obligations(
        &mut self,
        param_def: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<Vec<ParamTypeFactCheckResult>, ExecHaveObjInNonemptySetStmtFailed>>
    {
        let mut out = Vec::new();
        for group in &param_def.groups {
            let check = match &group.param_type {
                ParamType::Set(_) => ParamTypeFactCheckResult::Set,
                ParamType::NonemptySet(_) => ParamTypeFactCheckResult::NonemptySet,
                ParamType::FiniteSet(_) => ParamTypeFactCheckResult::FiniteSet,
                ParamType::Obj(param_set) => {
                    let nonempty_set = nonempty_check_set_for_param_obj(param_set);
                    let fact_id = self.global_ids.allocate_fact_id();
                    let fact = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                        fact_id,
                        set: nonempty_set,
                        line_file: None,
                    }));
                    let verify_result = self.verify_fact(&fact, verify_state.clone())?;
                    if verify_result.is_failed() {
                        return Ok(Err(ExecHaveObjInNonemptySetStmtFailed::NonemptyCheck(
                            verify_result,
                        )));
                    }
                    ParamTypeFactCheckResult::Obj(verify_result)
                }
            };
            out.push(check);
        }
        Ok(Ok(out))
    }
}

fn nonempty_check_set_for_param_obj(param_set: &Obj) -> Obj {
    match param_set {
        Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)) => fn_set.ret_set.as_ref().clone(),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => anon.body.ret_set.as_ref().clone(),
        _ => param_set.clone(),
    }
}
