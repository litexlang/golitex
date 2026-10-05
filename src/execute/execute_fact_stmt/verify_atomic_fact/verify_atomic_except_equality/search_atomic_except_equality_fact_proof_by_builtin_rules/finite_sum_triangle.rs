//! Triangle inequality for a finite real sum; whole-fact WD checks both carriers.
use crate::ast::fact::LessEqualFact;
use crate::ast::obj::{ArithmeticOperator, IteratedOperator, Obj};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::by_they_are_the_same::helper::compound_objs_alpha_equal;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::verify_equality_by_builtin_rules::helper::finite_abs_callback_matches;

pub struct FiniteSetSumTriangleProof {}

pub(super) fn search_finite_sum_triangle(
    fact: &LessEqualFact,
) -> Option<FiniteSetSumTriangleProof> {
    let Obj::ArithmeticOperator(ArithmeticOperator::Abs(abs)) = &fact.left else {
        return None;
    };
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(sum)) = abs.arg.as_ref() else {
        return None;
    };
    let Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(bound)) = &fact.right else {
        return None;
    };
    if !compound_objs_alpha_equal(&sum.set, &bound.set)
        || !finite_abs_callback_matches(&bound.func, &bound.set, &sum.func)
    {
        return None;
    }
    Some(FiniteSetSumTriangleProof {})
}
