use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact, InFact};
use crate::new_pipeline::ast::names::BoundName;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::param::{ParamType, TypedParameterList};
use crate::new_pipeline::ast::stmt::HaveObjEqualStmt;
use crate::new_pipeline::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::new_pipeline::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

pub enum ExecHaveObjEqualStmtFailed {
    ParamCountMismatch,
    ParamType(VerifyObjWellDefinedResult),
    EqualToWellDefined(VerifyObjWellDefinedResult),
    Membership(VerifyFactResult),
}

// Pipeline: check arity → WD param types → WD RHS → membership → define → store equals.
pub struct ExecHaveObjEqualStmtSuccessResult {
    pub statement: HaveObjEqualStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub equal_to_well_defined: Vec<VerifyObjWellDefinedResult>,
    pub membership_checks: Vec<VerifyFactResult>,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
}

pub enum ExecHaveObjEqualStmtResult {
    Success(ExecHaveObjEqualStmtSuccessResult),
    Failed(ExecHaveObjEqualStmtFailed),
}

impl ExecHaveObjEqualStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}

impl Runtime {
    // `have a R = 10` / `have a, b R = 10, 20`
    // Example: have a R = 10 stores `a $in R` and `a = 10` (ClosedNumericEqual indexes a).
    pub(super) fn exec_have_obj_equal_stmt(
        &mut self,
        stmt: &HaveObjEqualStmt,
    ) -> RuntimeResult<ExecHaveObjEqualStmtResult> {
        let bindings = flatten_typed_param_bindings(&stmt.param_def);
        if bindings.len() != stmt.objs_equal_to.len() {
            return Ok(ExecHaveObjEqualStmtResult::Failed(
                ExecHaveObjEqualStmtFailed::ParamCountMismatch,
            ));
        }

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
                return Ok(ExecHaveObjEqualStmtResult::Failed(
                    ExecHaveObjEqualStmtFailed::ParamType(failed),
                ));
            }
        };

        let mut equal_to_well_defined = Vec::with_capacity(stmt.objs_equal_to.len());
        for obj in &stmt.objs_equal_to {
            let wd = self.verify_obj_well_definedness(obj, verify_state.clone())?;
            if wd.is_failed() {
                return Ok(ExecHaveObjEqualStmtResult::Failed(
                    ExecHaveObjEqualStmtFailed::EqualToWellDefined(wd),
                ));
            }
            equal_to_well_defined.push(wd);
        }

        let mut membership_checks = Vec::with_capacity(bindings.len());
        for ((_, param_type), obj) in bindings.iter().zip(stmt.objs_equal_to.iter()) {
            match param_type {
                ParamType::Obj(param_set) => {
                    let fact_id = self.ids.allocate_fact_id();
                    let in_fact = InFact {
                        fact_id,
                        element: obj.clone(),
                        set: param_set.clone(),
                        line_file: Some(stmt.line_file.clone()),
                    };
                    let checked = self.verify_fact(
                        &Fact::AtomicFact(AtomicFact::InFact(in_fact)),
                        verify_state.clone(),
                    )?;
                    if checked.is_failed() {
                        return Ok(ExecHaveObjEqualStmtResult::Failed(
                            ExecHaveObjEqualStmtFailed::Membership(checked),
                        ));
                    }
                    membership_checks.push(checked);
                }
                ParamType::Set(_) | ParamType::NonemptySet(_) | ParamType::FiniteSet(_) => {
                    return Err(RuntimeError::Unsupported(
                        "new_pipeline `have ... =` currently supports only Obj param types (e.g. `have a R = 10`)"
                            .to_string(),
                    ));
                }
            }
        }

        let mut store_and_infer_result =
            self.define_typed_parameters_in_current_env(&stmt.param_def)?;

        for (binding, obj) in bindings.iter().zip(stmt.objs_equal_to.iter()) {
            let (name, _) = binding;
            let equality_fact_id = self.ids.allocate_fact_id();
            let left = Obj::Identifier(self.identifier_obj_for_stored_mention(name));
            let equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: equality_fact_id,
                left,
                right: obj.clone(),
                line_file: Some(stmt.line_file.clone()),
            }));
            let stored = self.store_fact_and_infer(&equal_fact)?;
            store_and_infer_result
                .stored_fact_ids
                .extend(stored.stored_fact_ids());
        }

        Ok(ExecHaveObjEqualStmtResult::Success(
            ExecHaveObjEqualStmtSuccessResult {
                statement: stmt.clone(),
                param_type_well_defined,
                equal_to_well_defined,
                membership_checks,
                store_and_infer_result,
            },
        ))
    }
}

fn flatten_typed_param_bindings(param_def: &TypedParameterList) -> Vec<(&BoundName, &ParamType)> {
    let mut out = Vec::new();
    for group in &param_def.groups {
        for param in &group.params {
            out.push((param, &group.param_type));
        }
    }
    out
}
