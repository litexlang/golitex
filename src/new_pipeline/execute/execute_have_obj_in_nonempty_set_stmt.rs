use super::exec_stmt_result::{
    ExecHaveObjInNonemptySetStmtResult, HaveObjGroupNonemptyCheckResult,
    StoreHaveObjAndInferResult,
};
use crate::new_pipeline::ast::fact::{
    AtomicFact, Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::obj::{AtomObj, Identifier, Obj};
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::ast::stmt::HaveObjInNonemptySetOrParamTypeStmt;
use crate::new_pipeline::execution_environment::helper::atomic_fact_id;
use crate::new_pipeline::execution_environment::SymbolDefinitionMemory;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // `have x S` / `have A nonempty_set` / …
    // 1. WD each param type
    // 2. prove nonempty obligations (Obj carriers only)
    // 3. define_symbol + store type facts
    pub(super) fn exec_have_obj_in_nonempty_set_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> RuntimeResult<ExecHaveObjInNonemptySetStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };

        let param_type_well_defined = self.verify_typed_parameters_well_definedness(
            &stmt.param_def,
            verify_state.clone(),
        )?;

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
                    HaveObjGroupNonemptyCheckResult::Obj(
                        self.verify_fact(&fact, verify_state.clone())?,
                    )
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
            for name in &group.params {
                if self.top_exec_env().lookup_symbol(name).is_some() {
                    return Err(RuntimeError::Invariant(format!(
                        "symbol `{name}` is already defined in this ExecEnv"
                    )));
                }
                self.top_exec_env_mut()
                    .define_symbol(name.clone(), SymbolDefinitionMemory {});

                let fact_id = self.ids.allocate_fact_id();
                let type_fact = type_fact_for_defined_param(
                    fact_id,
                    name,
                    &group.param_type,
                    stmt.line_file.clone(),
                );
                stored_fact_ids.push(atomic_fact_id(&type_fact));
                self.top_exec_env_mut()
                    .store_native_atomic_fact(type_fact);
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

fn identifier_obj(name: &str) -> Obj {
    Obj::Atom(AtomObj::Identifier(Identifier {
        name: name.to_string(),
    }))
}

fn type_fact_for_defined_param(
    fact_id: FactId,
    name: &str,
    param_type: &ParamType,
    line_file: LineFile,
) -> AtomicFact {
    let parameter = identifier_obj(name);
    match param_type {
        ParamType::Set(_) => AtomicFact::IsSetFact(IsSetFact {
            fact_id,
            set: parameter,
            line_file: Some(line_file),
        }),
        ParamType::NonemptySet(_) => AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
            fact_id,
            set: parameter,
            line_file: Some(line_file),
        }),
        ParamType::FiniteSet(_) => AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
            fact_id,
            set: parameter,
            line_file: Some(line_file),
        }),
        ParamType::Obj(set) => AtomicFact::InFact(InFact {
            fact_id,
            element: parameter,
            set: set.clone(),
            line_file: Some(line_file),
        }),
    }
}
