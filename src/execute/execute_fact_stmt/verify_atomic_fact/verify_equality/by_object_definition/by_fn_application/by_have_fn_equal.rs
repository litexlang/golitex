//! Equality by object definition: unfold `f(args)` when `f = fn(...) { body }` is known.
//!
//! Mathematical property:
//!   A stored equality path `f = ... = AnonymousFn` supplies the body,
//!   regardless of how `f` was introduced; then `f(args) = subst(body)`.
//!
//! Example:
//!   have fn id(x R) R = x
//!   have a R = 1
//!   id(a) = a

use crate::ast::fact::EqualFact;
use crate::ast::obj::{FnObj, FnObjHead, FunctionSpace, Obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::KnownEqualityPathProof;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::equivalence_class_members_with_paths_in_adjacency;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

use super::super::helper::{set_bound_parameter_count, set_bound_params_to_arg_map};

pub struct ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof {
    pub normalization: super::normalize_function_body::FunctionBodyNormalizationProof,
    pub residual_equal: VerifyFactResult,
}

pub struct AnonFnApplicationBodyProof {
    pub function_equal: KnownEqualityPathProof,
    pub expanded_body: Obj,
}

impl Runtime {
    // The definition route expands a bounded sequence of checked bodies and
    // verifies the residual with the caller's restricted premise permissions.

    pub(crate) fn try_unfold_named_have_fn_equal_application(
        &mut self,
        app_side: &Obj,
        other_side: &Obj,
        parent_fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof>> {
        let Some(normalization) =
            self.normalize_function_body(app_side, other_side, verify_state)?
        else {
            return Ok(None);
        };

        let residual = EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: normalization.expanded_body.clone(),
            right: other_side.clone(),
            line_file: parent_fact.line_file.clone(),
        };
        let child_state = verify_state.without_rewrite();
        let residual_equal = self.verify_equal_fact(&residual, child_state)?;
        if residual_equal.is_failed() {
            return Ok(None);
        }
        Ok(Some(
            ByUnfoldNamedHaveFnEqualApplicationObjectDefinitionProof {
                normalization,
                residual_equal,
            },
        ))
    }

    pub(crate) fn expanded_named_or_literal_anon_fn_application_body(
        &mut self,
        fn_obj: &FnObj,
    ) -> RuntimeResult<Option<AnonFnApplicationBodyProof>> {
        // Shared builtin/aggregate premises still request exactly one beta step.
        if fn_obj.body.len() != 1 {
            return Ok(None);
        }
        let fn_args: Vec<Obj> = fn_obj.body[0].iter().map(|a| a.as_ref().clone()).collect();

        let head_obj = match fn_obj.head.as_ref() {
            FnObjHead::AnonymousFnLiteral(anon) => {
                Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon.as_ref().clone()))
            }
            FnObjHead::Identifier(head) => Obj::Identifier(head.clone()),
            _ => return Ok(None),
        };
        // Stored equalities transport the function body, independently of how
        // the head was introduced. Example: g=f and f=anon justify g(4)=5.
        let members = equivalence_class_members_with_paths_in_adjacency(
            &self.visible_equivalence_class_adjacency(),
            &head_obj,
        );
        for (candidate, path) in members {
            let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) = &candidate else {
                continue;
            };
            if fn_args.len() != set_bound_parameter_count(&anon.body.set_bound_parameters) {
                continue;
            }
            let fn_subst = set_bound_params_to_arg_map(&anon.body.set_bound_parameters, &fn_args);
            let Ok(expanded_body) = self.inst_obj(anon.equal_to.as_ref(), &fn_subst) else {
                continue;
            };
            let function_equal = KnownEqualityPathProof::new(path);
            return Ok(Some(AnonFnApplicationBodyProof {
                function_equal,
                expanded_body,
            }));
        }
        Ok(None)
    }
}
