//! Equality by object definition: unfold `f(args)` from `have fn f by induc`.
//!
//! Mathematical property:
//!   If `have fn f(params) T by induc measure from lower:` stores nested case
//!   guards and bodies, and the concrete arguments prove a root-to-leaf path of
//!   guards, then `f(args)` equals that leaf body under the same substitution.
//!
//! Example:
//!   have fn countdown(n N) N by induc n from 0:
//!       case n = 0: 0
//!       case n >= 1: countdown(n - 1)
//!   countdown(0) = 0

use crate::new_pipeline::ast::fact::{and_chain_as_fact, EqualFact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::ast::stmt::{HaveFnByInducCase, HaveFnByInducCaseBody};
use crate::new_pipeline::exec_env::StoredIdentifierDefinition;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;
use std::rc::Rc;

use super::helper::{
    fn_app_name_and_args, set_bound_parameter_count, set_bound_params_to_arg_map,
};

pub struct ByUnfoldHaveFnByInducApplicationObjectDefinitionProof {
    pub expanded_body: Obj,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub fn search_equal_fact_object_definition_unfold_have_fn_by_induc_application(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByUnfoldHaveFnByInducApplicationObjectDefinitionProof>> {
        if let Some(proof) = self.try_unfold_have_fn_by_induc_application(
            &fact.left,
            &fact.right,
            fact,
            verify_state.clone(),
        )? {
            return Ok(Some(proof));
        }
        if let Some(proof) = self.try_unfold_have_fn_by_induc_application(
            &fact.right,
            &fact.left,
            fact,
            verify_state,
        )? {
            return Ok(Some(proof));
        }
        Ok(None)
    }

    fn try_unfold_have_fn_by_induc_application(
        &mut self,
        app_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByUnfoldHaveFnByInducApplicationObjectDefinitionProof>> {
        let Obj::FnObj(fn_obj) = app_side else {
            return Ok(None);
        };
        let Some((name, args)) = fn_app_name_and_args(fn_obj) else {
            return Ok(None);
        };
        let Some(StoredIdentifierDefinition::HaveFnByInduc((_, stmt))) =
            self.stored_identifier_definition_visible_in_stack(&name)
        else {
            return Ok(None);
        };
        let stmt = Rc::clone(stmt);
        let expected = set_bound_parameter_count(&stmt.fn_set_clause.set_bound_parameters);
        if args.len() != expected {
            return Ok(None);
        }
        let subst = set_bound_params_to_arg_map(&stmt.fn_set_clause.set_bound_parameters, &args);
        let Some(expanded_body) =
            self.match_induc_case_body(&stmt.cases, &subst, verify_state.clone())?
        else {
            return Ok(None);
        };

        let residual = EqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left: expanded_body.clone(),
            right: other_side.clone(),
            line_file: parent_fact.line_file.clone(),
        };
        let child_state = VerifyState {
            can_use_forall_fact: verify_state.can_use_forall_fact,
            can_use_rewrite: false,
            store_well_defined_fact: false,
        };
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(ByUnfoldHaveFnByInducApplicationObjectDefinitionProof {
            expanded_body,
            residual_equal,
        }))
    }

    fn match_induc_case_body(
        &mut self,
        cases: &[HaveFnByInducCase],
        subst: &HashMap<IdentifierId, Obj>,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<Obj>> {
        // Case guards often need arithmetic rewrite (e.g. `1 - 1 = 0`).
        // Do not inherit residual child's `can_use_rewrite: false`.
        let case_guard_state = VerifyState {
            can_use_forall_fact: verify_state.can_use_forall_fact,
            can_use_rewrite: true,
            store_well_defined_fact: false,
        };
        for case in cases {
            let Ok(inst_case) = self.inst_and_chain_atomic(&case.case_fact, subst) else {
                continue;
            };
            let case_check = self.verify_fact(&and_chain_as_fact(&inst_case), case_guard_state.clone())?;
            if case_check.is_failed() {
                continue;
            }
            match &case.body {
                HaveFnByInducCaseBody::EqualTo(equal_to) => {
                    let Ok(expanded_body) = self.inst_obj(equal_to, subst) else {
                        continue;
                    };
                    return Ok(Some(expanded_body));
                }
                HaveFnByInducCaseBody::NestedCases(nested) => {
                    if let Some(body) =
                        self.match_induc_case_body(nested, subst, verify_state.clone())?
                    {
                        return Ok(Some(body));
                    }
                }
            }
        }
        Ok(None)
    }
}
