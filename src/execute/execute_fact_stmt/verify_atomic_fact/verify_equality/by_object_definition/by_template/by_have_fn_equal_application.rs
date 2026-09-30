//! Equality by object definition: unfold `\Name<args>(…)` when the template body is `have fn … = …`.
//!
//! Mathematical property:
//!   If `template<params>:` defines `have fn name(…) T = body`, then
//!   `\name<args>(fn_args) = subst(body)` under the combined substitution.
//!
//! Example:
//!   template<S set, z S>:
//!       have fn const_on_S(x S) S = z
//!   \const_on_S<R, 0>(2) = 0

use crate::ast::fact::EqualFact;
use crate::ast::obj::{FnObj, FnObjHead, InstantiatedTemplateObj, Obj, FunctionSpace};
use crate::ast::stmt::TemplateDefEnum;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::{Runtime, RuntimeResult};
use std::collections::HashMap;

use super::super::helper::{set_bound_parameter_count, set_bound_params_to_arg_map};

pub struct ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof {
    pub expanded_body: Obj,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub(crate) fn try_unfold_instantiated_template_have_fn_equal_application(
        &mut self,
        app_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof>>
    {
        let Obj::FnObj(fn_obj) = app_side else {
            return Ok(None);
        };
        let FnObjHead::InstantiatedTemplateObj(inst) = fn_obj.head.as_ref() else {
            return Ok(None);
        };
        let Some(expanded_body) =
            self.expanded_have_fn_equal_application_body(inst, fn_obj)?
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
};
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            ByUnfoldInstantiatedTemplateHaveFnEqualApplicationObjectDefinitionProof {
                expanded_body,
                residual_equal,
            },
        ))
    }

    fn expanded_have_fn_equal_application_body(
        &mut self,
        inst: &InstantiatedTemplateObj,
        fn_obj: &FnObj,
    ) -> RuntimeResult<Option<Obj>> {
        let plain = inst.template_name.local_name();
        let Some(def) = self.def_template_visible_in_stack(plain) else {
            return Ok(None);
        };
        let TemplateDefEnum::HaveFnEqualStmt(have_fn) = &def.template_def_stmt else {
            return Ok(None);
        };
        if inst.args.len() != def.template_arg_def.ordered_param_ids().len() {
            return Ok(None);
        }
        // Single application layer only for this rule.
        if fn_obj.body.len() != 1 {
            return Ok(None);
        }
        let layer = &fn_obj.body[0];
        let fn_args: Vec<Obj> = layer.iter().map(|a| a.as_ref().clone()).collect();
        let expected = set_bound_parameter_count(&have_fn.equal_to_anonymous_fn.body.set_bound_parameters);
        if fn_args.len() != expected {
            return Ok(None);
        }

        let mut subst: HashMap<IdentifierId, Obj> = HashMap::new();
        for (id, arg) in def
            .template_arg_def
            .ordered_param_ids()
            .into_iter()
            .zip(inst.args.iter())
        {
            subst.insert(id, arg.clone());
        }
        let Ok(inst_anon) = self.inst_obj(
            &Obj::FunctionSpace(FunctionSpace::AnonymousFn(have_fn.equal_to_anonymous_fn.clone())),
            &subst,
        ) else {
            return Ok(None);
        };
        let Obj::FunctionSpace(FunctionSpace::AnonymousFn(inst_anon)) = inst_anon else {
            return Ok(None);
        };
        let fn_subst =
            set_bound_params_to_arg_map(&inst_anon.body.set_bound_parameters, &fn_args);
        match self.inst_obj(inst_anon.equal_to.as_ref(), &fn_subst) {
            Ok(body) => Ok(Some(body)),
            Err(_) => Ok(None),
        }
    }
}
