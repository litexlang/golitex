use crate::new_pipeline::ast::fact::{AtomicFact, Fact, IsNonemptySetFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::ast::stmt::HaveObjInNonemptySetOrParamTypeStmt;
use crate::new_pipeline::exec_env::DefinedIdentifierInfo;
use crate::new_pipeline::execute::execute_fact_stmt::{
    FailToVerifyWellDefinedResult, ParamTypeWellDefinedProof, VerifyFactResult,
    VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeError, RuntimeResult};

pub struct StoreHaveObjAndInferResult {
    pub stored_fact_ids: Vec<FactId>,
}

// One entry per TypedParameterGroup, mirroring ParamType.
pub enum HaveObjGroupNonemptyCheckResult {
    Set,
    NonemptySet,
    FiniteSet,
    Obj(VerifyFactResult),
}

pub enum ExecHaveObjInNonemptySetStmtFailed {
    ParamType(VerifyObjWellDefinedResult),
    NonemptyCheck(VerifyFactResult),
}

// Pipeline: WD param types → nonempty obligations → define symbols.
pub struct ExecHaveObjInNonemptySetStmtSuccessResult {
    pub statement: HaveObjInNonemptySetOrParamTypeStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub nonempty_checks: Vec<HaveObjGroupNonemptyCheckResult>,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
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
    pub(super) fn exec_have_obj_in_nonempty_set_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> RuntimeResult<ExecHaveObjInNonemptySetStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };

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
                return Ok(ExecHaveObjInNonemptySetStmtResult::Failed(
                    ExecHaveObjInNonemptySetStmtFailed::ParamType(failed),
                ));
            }
            kept_param_type_well_defined.push(proof);
        }
        let param_type_well_defined = kept_param_type_well_defined;

        let nonempty_checks =
            match self.verify_have_obj_nonempty_obligations(&stmt.param_def, verify_state)? {
                Ok(checks) => checks,
                Err(failed) => {
                    return Ok(ExecHaveObjInNonemptySetStmtResult::Failed(failed));
                }
            };

        let store_and_infer_result = self.affect_have_obj_in_nonempty_set_environment(stmt)?;

        Ok(ExecHaveObjInNonemptySetStmtResult::Success(
            ExecHaveObjInNonemptySetStmtSuccessResult {
                statement: stmt.clone(),
                param_type_well_defined,
                nonempty_checks,
                store_and_infer_result,
            },
        ))
    }

    fn verify_have_obj_nonempty_obligations(
        &mut self,
        param_def: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Result<Vec<HaveObjGroupNonemptyCheckResult>, ExecHaveObjInNonemptySetStmtFailed>>
    {
        let mut out = Vec::new();
        for group in &param_def.groups {
            let check = match &group.param_type {
                ParamType::Set(_) => HaveObjGroupNonemptyCheckResult::Set,
                ParamType::NonemptySet(_) => HaveObjGroupNonemptyCheckResult::NonemptySet,
                ParamType::FiniteSet(_) => HaveObjGroupNonemptyCheckResult::FiniteSet,
                ParamType::Obj(param_set) => {
                    let nonempty_set = nonempty_check_set_for_param_obj(param_set);
                    let fact_id = self.ids.allocate_fact_id();
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
                    HaveObjGroupNonemptyCheckResult::Obj(verify_result)
                }
            };
            out.push(check);
        }
        Ok(Ok(out))
    }

    fn affect_have_obj_in_nonempty_set_environment(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
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

fn nonempty_check_set_for_param_obj(param_set: &Obj) -> Obj {
    match param_set {
        Obj::FnSet(fn_set) => fn_set.alpha.ret_set.as_ref().clone(),
        Obj::AnonymousFn(anon) => anon.alpha.body.ret_set.as_ref().clone(),
        _ => param_set.clone(),
    }
}
