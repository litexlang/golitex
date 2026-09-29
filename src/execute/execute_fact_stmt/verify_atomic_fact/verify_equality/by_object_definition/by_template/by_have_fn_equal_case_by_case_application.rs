//! Equality by object definition: unfold `\Name<args>(…)` when the template
//! body is `have fn … by cases`.
//!
//! Mathematical property:
//!   If `template<params>:` defines `have fn name(…) T by cases:`, then
//!   `\name<args>(fn_args)` unfolds like the ordinary by-cases rule after
//!   substituting template parameters and function arguments.
//!
//! Example:
//!   template<a R>:
//!       have fn above_a(x R) Z by cases:
//!           case x > a: 1
//!           case x = a: 0
//!           case x < a: (-1)
//!   \above_a<0>(-2) = (-1)

use crate::ast::fact::EqualFact;
use crate::ast::obj::{FnObjHead, Obj};
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

use super::super::helper::{fn_app_args, set_bound_parameter_count, set_bound_params_to_arg_map};

pub struct ByUnfoldInstantiatedTemplateHaveFnEqualCaseByCaseApplicationObjectDefinitionProof {
    pub matched_case_index: usize,
    pub expanded_body: Obj,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub(crate) fn try_unfold_instantiated_template_have_fn_equal_case_by_case_application(
        &mut self,
        app_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Option<ByUnfoldInstantiatedTemplateHaveFnEqualCaseByCaseApplicationObjectDefinitionProof>,
    > {
        let Obj::FnObj(fn_obj) = app_side else {
            return Ok(None);
        };
        let FnObjHead::InstantiatedTemplateObj(inst) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        let Some(args) = fn_app_args(fn_obj) else {
            return Ok(None);
        };
        let plain = inst.template_name.local_name();

        let (stmt, subst) = {
            let Some(def) = self.def_template_visible_in_stack(plain) else {
                return Ok(None);
            };
            let TemplateDefEnum::HaveFnEqualCaseByCaseStmt(stmt) = &def.template_def_stmt else {
                return Ok(None);
            };
            let template_param_ids = def.template_arg_def.ordered_param_ids();
            if inst.args.len() != template_param_ids.len() {
                return Ok(None);
            }
            let expected = set_bound_parameter_count(&stmt.fn_set_clause.set_bound_parameters);
            if args.len() != expected || stmt.cases.len() != stmt.equal_tos.len() {
                return Ok(None);
            }
            let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
            for (id, arg) in template_param_ids.into_iter().zip(inst.args.iter()) {
                subst.insert(id, arg.clone());
            }
            for (id, arg) in set_bound_params_to_arg_map(
                &stmt.fn_set_clause.set_bound_parameters,
                &args,
            ) {
                subst.insert(id, arg);
            }
            (stmt.clone(), subst)
        };

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
            can_use_builtin_rule: verify_state.can_use_builtin_rule,
            can_use_def_and_known_forall_and_known_strategy: verify_state.can_use_def_and_known_forall_and_known_strategy,
            can_use_rewrite: false,
            store_well_defined_fact: false,
                    builtin_strategy_depth_remaining: verify_state.builtin_strategy_depth_remaining,
};
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            ByUnfoldInstantiatedTemplateHaveFnEqualCaseByCaseApplicationObjectDefinitionProof {
                matched_case_index,
                expanded_body,
                residual_equal,
            },
        ))
    }
}
