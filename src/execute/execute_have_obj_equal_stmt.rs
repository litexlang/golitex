use crate::ast::fact::{
    AtomicFact, EqualFact, Fact, InFact, IsFiniteSetFact, IsNonemptySetFact, IsSetFact,
};
use crate::ast::names::BoundName;
use crate::ast::obj::Obj;
use crate::ast::param::{ParamType, TypedParameterList};
use crate::ast::stmt::HaveObjEqualStmt;
use crate::execute::exec_stmt_result::ParamTypeWellDefinedProof;
use crate::execute::execute_fact_stmt::{
    VerifyFactResult, VerifyObjWellDefinedResult, VerifyState,
};
use crate::execute::execute_have_obj_in_nonempty_set_stmt::StoreHaveObjAndInferResult;
use crate::execute::introduce_typed_parameters::SharedHaveDefinition;
use crate::runtime::{Runtime, RuntimeResult};
use std::rc::Rc;

pub enum ExecHaveObjEqualStmtFailed {
    ParamCountMismatch,
    ParamType(VerifyObjWellDefinedResult),
    EqualToWellDefined(VerifyObjWellDefinedResult),
    Membership(VerifyFactResult),
    AutoOpenStructLayer(crate::execute::FailToReleaseOneStructLayer),
}

// Pipeline: check arity → WD param types → WD RHS → membership → define → store equals.
pub struct ExecHaveObjEqualStmtSuccessResult {
    pub statement: HaveObjEqualStmt,
    pub param_type_well_defined: Vec<ParamTypeWellDefinedProof>,
    pub equal_to_well_defined: Vec<VerifyObjWellDefinedResult>,
    pub membership_checks: Vec<VerifyFactResult>,
    pub store_and_infer_result: StoreHaveObjAndInferResult,
    pub auto_opened_struct_layers:
        Option<Vec<crate::execute::ReleaseOneStructLayerProof>>,
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
    // `have a R = 10` / `have a, b R = 10, 20` / `have S set = T`
    // Example: have a R = 10 stores `a $in R` and `a = 10` (known_closed_numeric_equal indexes a).
    // Example: have carrier_copy set = S stores `$is_set(carrier_copy)` and `carrier_copy = S`.
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
            can_use_def_and_known_forall_and_known_strategy: true,
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
            let type_fact = match param_type {
                ParamType::Obj(param_set) => Fact::AtomicFact(AtomicFact::InFact(InFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    element: obj.clone(),
                    set: param_set.clone(),
                    line_file: Some(stmt.line_file.clone()),
                })),
                ParamType::Set(_) => Fact::AtomicFact(AtomicFact::IsSetFact(IsSetFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    set: obj.clone(),
                    line_file: Some(stmt.line_file.clone()),
                })),
                ParamType::NonemptySet(_) => {
                    Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        set: obj.clone(),
                        line_file: Some(stmt.line_file.clone()),
                    }))
                }
                ParamType::FiniteSet(_) => {
                    Fact::AtomicFact(AtomicFact::IsFiniteSetFact(IsFiniteSetFact {
                        fact_id: self.global_ids.allocate_fact_id(),
                        set: obj.clone(),
                        line_file: Some(stmt.line_file.clone()),
                    }))
                }
            };
            let checked = self.verify_fact(&type_fact, verify_state.clone())?;
            if checked.is_failed() {
                return Ok(ExecHaveObjEqualStmtResult::Failed(
                    ExecHaveObjEqualStmtFailed::Membership(checked),
                ));
            }
            membership_checks.push(checked);
        }

        let mut store_and_infer_result = self.define_typed_parameters_in_current_env(
            &stmt.param_def,
            Some(SharedHaveDefinition::HaveObjEqual(Rc::new(stmt.clone()))),
        )?;

        let auto_opened_struct_layers =
            match self.auto_open_struct_layers_for_typed_parameters(&stmt.param_def)? {
                Ok(layers) => layers,
                Err((_, failed)) => {
                    return Ok(ExecHaveObjEqualStmtResult::Failed(
                        ExecHaveObjEqualStmtFailed::AutoOpenStructLayer(failed),
                    ));
                }
            };

        for (binding, obj) in bindings.iter().zip(stmt.objs_equal_to.iter()) {
            let (name, _) = binding;
            let equality_fact_id = self.global_ids.allocate_fact_id();
            let left = Obj::Identifier(self.identifier_obj_for_stored_mention(name));
            let equal_fact = Fact::AtomicFact(AtomicFact::EqualFact(EqualFact {
                fact_id: equality_fact_id,
                left,
                right: obj.clone(),
                line_file: Some(stmt.line_file.clone()),
            }));
            let stored = self.store_fact_and_infer(&equal_fact)?;
            if let Fact::AtomicFact(AtomicFact::EqualFact(eq)) = &equal_fact {
                self.record_fn_signature_from_definition_equal(eq);
            }
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
                auto_opened_struct_layers,
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
