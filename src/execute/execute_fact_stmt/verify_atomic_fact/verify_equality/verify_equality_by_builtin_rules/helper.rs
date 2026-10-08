//! Structural equality matchers and bounded log-algebra prerequisite helpers.
use super::reduce_rule_helper::reduce_application;
use crate::ast::obj::{FnObjHead, FunctionSpace, IdentifierObj, Obj, StructAndFieldAccessObj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal;

// q*pi-x and q*pi+(-x) share the same exact reflection matcher.
// Only an exact numeric pi coefficient is accepted; symbols need other rules.
pub(super) fn pi_reflection_argument(argument: &Obj, half_turn: bool) -> Option<&Obj> {
    use crate::ast::obj::{ArithmeticOperator as A, Literal, Number};
    let expected = Obj::Literal(Literal::Number(Number::new(
        if half_turn { "1" } else { "0.5" }.into(),
    )));
    let matches_shift = |shift: &Obj| {
        crate::rational_expression::pi_multiple::pi_coefficient(shift).is_some_and(|actual| {
            crate::rational_expression::objs_equal_by_rational_expression_evaluation(
                &actual, &expected,
            )
        })
    };
    match argument {
        Obj::ArithmeticOperator(A::Sub(difference)) if matches_shift(&difference.left) => {
            Some(&difference.right)
        }
        Obj::ArithmeticOperator(A::Add(sum)) => {
            for (shift, negative) in [(&*sum.left, &*sum.right), (&*sum.right, &*sum.left)] {
                if !matches_shift(shift) {
                    continue;
                }
                if let Obj::ArithmeticOperator(A::Neg(negation)) = negative {
                    return Some(&negation.arg);
                }
            }
            None
        }
        _ => None,
    }
}

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
        FnObjHead::Object(obj) => obj.as_ref().clone(),
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

use super::log_algebra_base_proof::{
    LogAlgebraBaseProof, LogAlgebraBelowOneProof, LogAlgebraPositiveNonunitProof,
};
use crate::ast::fact::{Fact, GreaterFact, LessFact, NotEqualFact};
use crate::ast::obj::{Literal, Number};
use crate::execute::execute_fact_stmt::{VerifyFactResult, VerifyState};
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Keep the former >1 route first; the two other guards describe the same
    // real-positive nonunit log domain. Every child inherits the caller ceiling.
    pub(crate) fn verify_log_algebra_base_guard(
        &mut self,
        base: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<Option<LogAlgebraBaseProof>> {
        let one = Obj::Literal(Literal::Number(Number::new("1".into())));
        let above_one = self.verify_order_gt_one(base, state)?;
        if !above_one.is_failed() {
            return Ok(Some(LogAlgebraBaseProof::GreaterThanOne(above_one)));
        }
        let reverse_above: Fact = GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: base.clone(),
            right: one.clone(),
            line_file: None,
        }
        .into();
        let above_one = self.verify_builtin_rule_premise(&reverse_above, state)?;
        if !above_one.is_failed() {
            return Ok(Some(LogAlgebraBaseProof::GreaterThanOne(above_one)));
        }
        let positive = self.verify_log_algebra_positive(base, state)?;
        if positive.is_failed() {
            return Ok(None);
        }
        let below: Fact = LessFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: base.clone(),
            right: one.clone(),
            line_file: None,
        }
        .into();
        let below_one = self.verify_builtin_rule_premise(&below, state)?;
        let below_one = if below_one.is_failed() {
            let reverse: Fact = GreaterFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: one.clone(),
                right: base.clone(),
                line_file: None,
            }
            .into();
            self.verify_builtin_rule_premise(&reverse, state)?
        } else {
            below_one
        };
        if !below_one.is_failed() {
            return Ok(Some(LogAlgebraBaseProof::BelowOne(
                LogAlgebraBelowOneProof::new(positive, below_one),
            )));
        }
        let nonunit: Fact = NotEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: base.clone(),
            right: one.clone(),
            line_file: None,
        }
        .into();
        let nonunit = self.verify_builtin_rule_premise(&nonunit, state)?;
        let nonunit = if nonunit.is_failed() {
            let reverse: Fact = NotEqualFact {
                fact_id: self.global_ids.allocate_fact_id(),
                left: one,
                right: base.clone(),
                line_file: None,
            }
            .into();
            self.verify_builtin_rule_premise(&reverse, state)?
        } else {
            nonunit
        };
        if nonunit.is_failed() {
            return Ok(None);
        }
        Ok(Some(LogAlgebraBaseProof::PositiveNonunit(
            LogAlgebraPositiveNonunitProof::new(positive, nonunit),
        )))
    }

    // Preserve the actual positive source spelling and its FactId.
    // Example: x>0 can supply the log argument guard without nested conversion.
    pub(crate) fn verify_log_algebra_positive(
        &mut self,
        obj: &Obj,
        state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let positive = self.verify_order_positive(obj, state)?;
        if !positive.is_failed() {
            return Ok(positive);
        }
        let reverse: Fact = GreaterFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: obj.clone(),
            right: Obj::Literal(Literal::Number(Number::new("0".into()))),
            line_file: None,
        }
        .into();
        self.verify_builtin_rule_premise(&reverse, state)
    }
}
