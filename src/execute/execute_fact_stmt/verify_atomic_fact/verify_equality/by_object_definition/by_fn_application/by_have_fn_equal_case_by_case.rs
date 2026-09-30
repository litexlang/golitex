//! Equality by object definition: unfold `f(args)` from `have fn f by cases`.
//!
//! Mathematical property:
//!   If `have fn f(params) T by cases:` stores case guards `C_i` and bodies `B_i`,
//!   and the concrete arguments prove some `C_k[args/params]`, then
//!   `f(args) = B_k[args/params]`.
//!
//! Example:
//!   have fn sign_value(x R) Z by cases:
//!       case x > 0: 1
//!       case x = 0: 0
//!       case x < 0: (-1)
//!   sign_value(-2) = (-1)

use crate::ast::fact::{and_chain_as_fact, EqualFact};
use crate::ast::obj::Obj;
use crate::ast::stmt::HaveFnEqualCaseByCaseStmt;
use crate::exec_env::StoredIdentifierDefinition;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};
use crate::runtime::runtime_ids::IdentifierId;
use std::collections::HashMap;
use std::rc::Rc;

use super::super::helper::{
    fn_app_name_and_args, set_bound_parameter_count, set_bound_params_to_arg_map,
};

pub struct ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof {
    pub matched_case_index: usize,
    pub expanded_body: Obj,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub(crate) fn try_unfold_have_fn_equal_case_by_case_application(
        &mut self,
        app_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof>> {
        let Obj::FnObj(fn_obj) = app_side else {
            return Ok(None);
        };
        let Some((name, args)) = fn_app_name_and_args(fn_obj) else {
            return Ok(None);
        };
        let Some(StoredIdentifierDefinition::HaveFnEqualCaseByCase((_, stmt))) =
            self.stored_identifier_definition_visible_in_stack(&name)
        else {
            return Ok(None);
        };
        let stmt = Rc::clone(stmt);
        let expected = set_bound_parameter_count(&stmt.fn_set_clause.set_bound_parameters);
        if args.len() != expected || stmt.cases.len() != stmt.equal_tos.len() {
            return Ok(None);
        }
        let subst = set_bound_params_to_arg_map(&stmt.fn_set_clause.set_bound_parameters, &args);
        let Some((matched_case_index, expanded_body)) =
            self.match_case_by_case_body(&stmt, &subst, verify_state.clone())?
        else {
            return Ok(None);
        };

        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: expanded_body.clone(),
            right: other_side.clone(),
            line_file: parent_fact.line_file.clone(),
        };
        let child_state = VerifyState {
            can_use_builtin_rule_round: verify_state.can_use_builtin_rule_round,
            can_use_def_and_known_forall_and_known_strategy: verify_state.can_use_def_and_known_forall_and_known_strategy,
            can_use_rewrite: false,
            store_well_defined_fact: false,
            equality_class_search: verify_state.equality_class_search,
};
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            ByUnfoldHaveFnEqualCaseByCaseApplicationObjectDefinitionProof {
                matched_case_index,
                expanded_body,
                residual_equal,
            },
        ))
    }

    // Shared with template have-fn-by-cases unfold: `subst` may already include
    // template-parameter bindings.
    pub(crate) fn match_case_by_case_body(
        &mut self,
        stmt: &HaveFnEqualCaseByCaseStmt,
        subst: &HashMap<IdentifierId, Obj>,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<(usize, Obj)>> {
        // Case guards often need arithmetic rewrite (e.g. `1 - 1 = 0`).
        // Do not inherit residual child's `can_use_rewrite: false`.
        let case_guard_state = VerifyState {
            can_use_builtin_rule_round: verify_state.can_use_builtin_rule_round,
            can_use_def_and_known_forall_and_known_strategy: verify_state.can_use_def_and_known_forall_and_known_strategy,
            can_use_rewrite: true,
            store_well_defined_fact: false,
            equality_class_search: verify_state.equality_class_search,
};
        for (i, (case_fact, equal_to)) in stmt.cases.iter().zip(stmt.equal_tos.iter()).enumerate() {
            let Ok(inst_case) = self.inst_and_chain_atomic(case_fact, subst) else {
                continue;
            };
            let case_check = self.verify_fact(&and_chain_as_fact(&inst_case), case_guard_state.clone())?;
            if case_check.is_failed() {
                continue;
            }
            let Ok(expanded_body) = self.inst_obj(equal_to, subst) else {
                continue;
            };
            return Ok(Some((i, expanded_body)));
        }
        Ok(None)
    }
}
