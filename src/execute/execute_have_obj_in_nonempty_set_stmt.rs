use crate::ast::fact::{AtomicFact, Fact, IsNonemptySetFact};
use crate::ast::param::{ParamType, TypedParameterList};
use crate::ast::stmt::HaveObjInNonemptySetOrParamTypeStmt;
use crate::execute::exec_stmt_result::{ParamTypeFactCheckResult, ParamTypeWellDefinedProof};
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::introduce_typed_parameters::SharedHaveDefinition;
use crate::runtime::{FactId, Runtime, RuntimeResult};
use crate::store_fact_and_infer::StoreFactAndInferResult;
use std::rc::Rc;

pub struct StoreHaveObjAndInferResult {
    pub store_and_infer_results: Vec<Rc<StoreFactAndInferResult>>,
    pub stored_fact_ids: Vec<FactId>,
}

impl StoreHaveObjAndInferResult {
    // Actual ordered stores own the proof; IDs remain the existing flattened view.
    pub fn new(store_and_infer_results: Vec<Rc<StoreFactAndInferResult>>) -> Self {
        let stored_fact_ids = store_and_infer_results
            .iter()
            .flat_map(|stored| stored.stored_fact_ids())
            .collect();
        Self {
            store_and_infer_results,
            stored_fact_ids,
        }
    }

    pub fn push(&mut self, stored: StoreFactAndInferResult) {
        self.stored_fact_ids.extend(stored.stored_fact_ids());
        self.store_and_infer_results.push(Rc::new(stored));
    }

    pub fn extend(&mut self, other: Self) {
        self.stored_fact_ids.extend(other.stored_fact_ids);
        self.store_and_infer_results
            .extend(other.store_and_infer_results);
    }

    pub fn extend_shared(&mut self, other: &Self) {
        self.stored_fact_ids
            .extend(other.stored_fact_ids.iter().copied());
        self.store_and_infer_results
            .extend(other.store_and_infer_results.iter().map(Rc::clone));
    }
}

pub enum ExecHaveObjInNonemptySetStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    NonemptyCheck(VerifyFactResult),
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
}

// Each group: WD type → prove nonempty → define symbols; then auto-open.
pub struct HaveObjInNonemptySetGroupResult {
    pub param_type_well_defined: ParamTypeWellDefinedProof,
    pub nonempty_check: ParamTypeFactCheckResult,
    pub defined_params: StoreHaveObjAndInferResult,
}

pub struct ExecHaveObjInNonemptySetStmtSuccessResult {
    pub statement: HaveObjInNonemptySetOrParamTypeStmt,
    pub groups: Vec<HaveObjInNonemptySetGroupResult>,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
    pub auto_opened_struct_layers: Option<Vec<crate::execute::ReleaseOneStructLayerProof>>,
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
        let verify_state = VerifyState::top_level();

        let mut groups = Vec::with_capacity(stmt.param_def.groups.len());
        let mut store_and_infer_result = StoreHaveObjAndInferResult::new(Vec::new());
        let shared = Rc::new(stmt.clone());
        for group in &stmt.param_def.groups {
            let one = TypedParameterList {
                groups: vec![group.clone()],
            };
            let param_type_well_defined = match self
                .verify_typed_parameters_well_definedness_or_fail(&one, verify_state.clone())?
            {
                Ok(mut proofs) => proofs.remove(0),
                Err(failed) => {
                    return Ok(ExecHaveObjInNonemptySetStmtResult::Failed(
                        ExecHaveObjInNonemptySetStmtFailed::ParamType(failed),
                    ))
                }
            };
            let nonempty_check =
                match self.verify_have_obj_nonempty_obligations(&one, verify_state.clone())? {
                    Ok(mut checks) => checks.remove(0),
                    Err(failed) => return Ok(ExecHaveObjInNonemptySetStmtResult::Failed(failed)),
                };
            let defined_params = self.define_typed_parameters_in_current_env(
                &one,
                Some(SharedHaveDefinition::HaveObjInNonemptySetOrParamType(
                    Rc::clone(&shared),
                )),
                crate::execute::execute_fact_stmt::VerifyState::top_level(),
            )?;
            store_and_infer_result.extend_shared(&defined_params);
            groups.push(HaveObjInNonemptySetGroupResult {
                param_type_well_defined,
                nonempty_check,
                defined_params,
            });
        }
        let auto_opened_struct_layers = match self.auto_open_struct_layers_for_typed_parameters(
            &stmt.param_def,
            crate::execute::execute_fact_stmt::VerifyState::top_level(),
        )? {
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
                groups,
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
                    let fact_id = self.global_ids.allocate_fact_id();
                    let fact = Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                        fact_id,
                        set: param_set.clone(),
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

#[cfg(test)]
#[path = "../../tests/unit/execute/dependent_have/tests.rs"]
mod dependent_have_tests;

#[cfg(test)]
#[path = "../../tests/unit/execute/producer_numeric_capture/tests.rs"]
mod producer_numeric_capture_tests;
