//! Equality by object definition: unfold `\Name<args>(…)` when the template
//! body is `have fn … by induc`.
//!
//! Mathematical property:
//!   If `template<params>:` defines `have fn name(…) T by induc …:`, then
//!   `\name<args>(fn_args)` unfolds like the ordinary by-induc rule after
//!   substituting template parameters and function arguments.
//!
//! Recursive bodies written with the plain name `name(…)` (required while the
//! template is being checked) are rewritten to `\name<args>(…)` in the
//! residual so further unfolds stay on the template surface.
//!
//! Example:
//!   template<_S set>:
//!       have fn countdown_t(n N) N by induc n from 0:
//!           case n = 0: 0
//!           case n >= 1: countdown_t(n - 1)
//!   \countdown_t<{0}>(0) = 0
//!   \countdown_t<{0}>(1) = 0

use crate::ast::fact::EqualFact;
use crate::ast::obj::{FnObjHead, Obj};
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

use super::super::helper::{fn_app_args, set_bound_parameter_count, set_bound_params_to_arg_map};

pub struct ByUnfoldInstantiatedTemplateHaveFnByInducApplicationObjectDefinitionProof {
    pub expanded_body: Obj,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub(crate) fn try_unfold_instantiated_template_have_fn_by_induc_application(
        &mut self,
        app_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<
        Option<ByUnfoldInstantiatedTemplateHaveFnByInducApplicationObjectDefinitionProof>,
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

        let (stmt, subst) = {
            let Some(def) = self.def_template_visible(&inst.template_name) else {
                return Ok(None);
            };
            let TemplateDefEnum::HaveFnByInducStmt(stmt) = &def.template_def_stmt else {
                return Ok(None);
            };
            let template_param_ids = def.template_arg_def.ordered_param_ids();
            if inst.args.len() != template_param_ids.len() {
                return Ok(None);
            }
            let expected = set_bound_parameter_count(&stmt.fn_set_clause.set_bound_parameters);
            if args.len() != expected {
                return Ok(None);
            }
            let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
            for (id, arg) in template_param_ids.into_iter().zip(inst.args.iter()) {
                subst.insert(id, arg.clone());
            }
            for (id, arg) in
                set_bound_params_to_arg_map(&stmt.fn_set_clause.set_bound_parameters, &args)
            {
                subst.insert(id, arg);
            }
            (stmt.clone(), subst)
        };

        let Some(raw_body) =
            self.match_induc_case_body(&stmt.cases, &subst, verify_state.clone())?
        else {
            return Ok(None);
        };
        // Use capture-safe substitution through every object constructor.
        // A recursive call under `+`, a tuple, or a lambda keeps this template instance.
        let mut recursive_subst = HashMap::new();
        recursive_subst.insert(stmt.name.id, Obj::InstantiatedTemplateObj(inst.clone()));
        let Ok(expanded_body) = self.inst_obj(&raw_body, &recursive_subst) else {
            return Ok(None);
        };

        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: expanded_body.clone(),
            right: other_side.clone(),
            line_file: parent_fact.line_file.clone(),
        };
        let child_state = verify_state.without_rewrite();
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            ByUnfoldInstantiatedTemplateHaveFnByInducApplicationObjectDefinitionProof {
                expanded_body,
                residual_equal,
            },
        ))
    }
}
