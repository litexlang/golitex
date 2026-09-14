use super::exec_stmt_result::{
    ExecHaveObjInNonemptySetStmtResult, HaveObjGroupNonemptyCheckResult, StoreHaveObjAndInferResult,
};
use crate::new_pipeline::ast::fact::{AtomicFact, Fact, IsNonemptySetFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::ast::stmt::HaveObjInNonemptySetOrParamTypeStmt;
use crate::new_pipeline::exec_env::DefinedIdentifierInfo;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // `have x S` / `have A nonempty_set` / …
    // 1. WD each param type
    // 2. prove nonempty obligations (Obj carriers only)
    // 3. record symbols; type-fact ids go in the result (facts store not wired yet)
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

        let nonempty_checks =
            self.verify_have_obj_nonempty_obligations(&stmt.param_def, verify_state)?;

        let store_and_infer_result = self.affect_have_obj_in_nonempty_set_environment(stmt)?;

        Ok(ExecHaveObjInNonemptySetStmtResult {
            statement: stmt.clone(),
            param_type_well_defined,
            nonempty_checks,
            store_and_infer_result,
        })
    }

    fn verify_have_obj_nonempty_obligations(
        &mut self,
        param_def: &TypedParameterList,
        verify_state: VerifyState,
    ) -> RuntimeResult<Vec<HaveObjGroupNonemptyCheckResult>> {
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
                    if verify_result.is_unknown() {
                        return Err(RuntimeError::Unknown(
                            "have: unable to prove carrier set is nonempty".to_string(),
                        ));
                    }
                    HaveObjGroupNonemptyCheckResult::Obj(verify_result)
                }
            };
            out.push(check);
        }
        Ok(out)
    }

    fn affect_have_obj_in_nonempty_set_environment(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> RuntimeResult<StoreHaveObjAndInferResult> {
        let mut stored_fact_ids = Vec::new();
        for group in &stmt.param_def.groups {
            for identifier in &group.params {
                if self
                    .top_exec_env()
                    .definitions
                    .identifiers
                    .contains_key(&identifier.identifier_id)
                {
                    return Err(RuntimeError::Invariant(format!(
                        "identifier `{}` is already defined in this ExecEnv",
                        identifier.name
                    )));
                }
                self.top_exec_env_mut().definitions.identifiers.insert(
                    identifier.identifier_id,
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

fn nonempty_check_set_for_param_obj(param_set: &Obj) -> Obj {
    match param_set {
        Obj::FnSet(fn_set) => fn_set.body.ret_set.as_ref().clone(),
        Obj::AnonymousFn(anon) => anon.body.ret_set.as_ref().clone(),
        _ => param_set.clone(),
    }
}
