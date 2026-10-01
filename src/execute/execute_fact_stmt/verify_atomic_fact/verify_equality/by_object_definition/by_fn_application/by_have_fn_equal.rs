//! Equality by object definition: unfold `f(args)` when `f = fn(...) { body }` is known.
//!
//! Mathematical property:
//!   If `have fn f(params) T = body` (or `let f = fn(...) { body }`) stores
//!   `f = AnonymousFn`, then `f(args) = subst(body)`.
//!
//! Example:
//!   have fn id(x R) R = x
//!   have a R = 1
//!   id(a) = a

use crate::ast::fact::EqualFact;
use crate::ast::obj::{FnObj, FnObjHead, FunctionSpace, Obj};
use crate::exec_env::exec_env::SpecialObjectPropertyByDefinition;
use crate::exec_env::StoredIdentifierDefinition;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

use super::super::helper::{set_bound_parameter_count, set_bound_params_to_arg_map};

pub struct ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof {
    pub expanded_body: Obj,
    pub residual_equal: VerifyFactResult,
}

impl Runtime {
    pub(crate) fn try_unfold_named_have_fn_equal_application(
        &mut self,
        app_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof>> {
        let Obj::FnObj(fn_obj) = app_side else {
            return Ok(None);
        };
        let Some(expanded_body) =
            self.expanded_named_or_literal_anon_fn_application_body(fn_obj)?
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
            ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof {
                expanded_body,
                residual_equal,
            },
        ))
    }

    pub(crate) fn expanded_named_or_literal_anon_fn_application_body(
        &mut self,
        fn_obj: &FnObj,
    ) -> RuntimeResult<Option<Obj>> {
        if fn_obj.body.len() != 1 {
            return Ok(None);
        }
        let fn_args: Vec<Obj> = fn_obj.body[0].iter().map(|a| a.as_ref().clone()).collect();

        let anon = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(anon) => anon.as_ref().clone(),
            FnObjHead::Identifier(head) => {
                if let Some(anon) = self.anonymous_fn_from_have_fn_equal_definition(head) {
                    anon
                } else {
                    let head_obj = Obj::Identifier(head.clone());
                    let Some(Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon))) =
                        self.visible_equal_to_function_obj(&head_obj)
                    else {
                        return Ok(None);
                    };
                    anon
                }
            }
            _ => return Ok(None),
        };

        let expected = set_bound_parameter_count(&anon.body.set_bound_parameters);
        if fn_args.len() != expected {
            return Ok(None);
        }
        let fn_subst = set_bound_params_to_arg_map(&anon.body.set_bound_parameters, &fn_args);
        match self.inst_obj(anon.equal_to.as_ref(), &fn_subst) {
            Ok(body) => Ok(Some(body)),
            Err(_) => Ok(None),
        }
    }

    fn anonymous_fn_from_have_fn_equal_definition(
        &self,
        head: &crate::ast::obj::IdentifierObj,
    ) -> Option<crate::ast::obj::AnonymousFn> {
        let StoredIdentifierDefinition::HaveFnEqual((_, stmt)) =
            self.stored_identifier_definition_visible(head)?
        else {
            return None;
        };
        Some(stmt.equal_to_anonymous_fn.clone())
    }

    fn visible_equal_to_function_obj(&self, obj: &Obj) -> Option<Obj> {
        let key = obj.ir();
        for env in self.execution_environments_stack.iter().rev() {
            let Some(props) = env.special_object_properties_by_def.get(&key) else {
                continue;
            };
            for prop in props {
                if let SpecialObjectPropertyByDefinition::EqualToFunction((fun, _)) = prop {
                    return Some(fun.clone());
                }
            }
        }
        None
    }
}
