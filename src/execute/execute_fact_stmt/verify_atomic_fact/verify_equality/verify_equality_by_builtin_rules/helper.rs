//! Structural pullback matching shared by finite reindex rules; no proof search.
use super::reduce_rule_helper::reduce_application;
use crate::ast::obj::{FnObjHead, FunctionSpace, IdentifierObj, Obj, StructAndFieldAccessObj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal;

pub(super) fn finite_restriction_matches(function: &Obj, domain: &Obj, source: &Obj) -> bool {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anonymous)) = function else {
        return false;
    };
    let [group] = anonymous.body.set_bound_parameters.groups.as_slice() else {
        return false;
    };
    let [parameter] = group.params.as_slice() else {
        return false;
    };
    if !anonymous.body.dom_facts.is_empty() || !compound_objs_alpha_equal(&group.param_type, domain)
    {
        return false;
    }
    let index = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
    let Some(expected) = reduce_application(source, vec![index]) else {
        return false;
    };
    compound_objs_alpha_equal(&anonymous.equal_to, &expected)
}

// The triangle bound needs the pointwise absolute value of precisely the
// original summand, including its actual bound identifier and callable head.
pub(in crate::execute::execute_fact_stmt::verify_atomic_fact) fn finite_abs_callback_matches(
    function: &Obj,
    domain: &Obj,
    source: &Obj,
) -> bool {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anonymous)) = function else {
        return false;
    };
    let [group] = anonymous.body.set_bound_parameters.groups.as_slice() else {
        return false;
    };
    let [parameter] = group.params.as_slice() else {
        return false;
    };
    if !anonymous.body.dom_facts.is_empty() || !compound_objs_alpha_equal(&group.param_type, domain)
    {
        return false;
    }
    let Obj::ArithmeticOperator(crate::ast::obj::ArithmeticOperator::Abs(abs)) =
        anonymous.equal_to.as_ref()
    else {
        return false;
    };
    let index = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
    let Some(expected) = reduce_application(source, vec![index]) else {
        return false;
    };
    compound_objs_alpha_equal(&abs.arg, &expected)
}

pub(super) fn finite_pullback_map(function: &Obj, domain: &Obj, source: &Obj) -> Option<Obj> {
    let Obj::FunctionSpace(FunctionSpace::AnonymousFn(anonymous)) = function else {
        return None;
    };
    let [group] = anonymous.body.set_bound_parameters.groups.as_slice() else {
        return None;
    };
    let [parameter] = group.params.as_slice() else {
        return None;
    };
    if !anonymous.body.dom_facts.is_empty() || !compound_objs_alpha_equal(&group.param_type, domain)
    {
        return None;
    }
    let Obj::FnObj(outer_call) = anonymous.equal_to.as_ref() else {
        return None;
    };
    let [argument] = outer_call.body.last()?.as_slice() else {
        return None;
    };
    let Obj::FnObj(map_call) = argument.as_ref() else {
        return None;
    };
    let [index] = map_call.body.last()?.as_slice() else {
        return None;
    };
    let bound = Obj::Identifier(IdentifierObj::from_bound_name(parameter));
    if index.as_ref() != &bound {
        return None;
    }
    let expected = reduce_application(source, vec![argument.as_ref().clone()])?;
    if !compound_objs_alpha_equal(anonymous.equal_to.as_ref(), &expected) {
        return None;
    }
    let mut map = map_call.clone();
    map.body.pop();
    if !map.body.is_empty() {
        return Some(Obj::FnObj(map));
    }
    Some(match map.head.as_ref() {
        FnObjHead::Identifier(id) => Obj::Identifier(id.clone()),
        FnObjHead::AnonymousFnLiteral(function) => {
            Obj::FunctionSpace(FunctionSpace::AnonymousFn(function.as_ref().clone()))
        }
        FnObjHead::FieldAccess(field) => {
            Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(field.clone()))
        }
        FnObjHead::InstantiatedTemplateObj(template) => {
            Obj::InstantiatedTemplateObj(template.clone())
        }
    })
}
