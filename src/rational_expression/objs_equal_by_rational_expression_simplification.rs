use crate::prelude::*;
use crate::rational_expression::collect_monomials::collect_monomials_in_obj;
use crate::rational_expression::monomial::MonomialWithNonZeroScalarAndOrderedOperands;
use crate::rational_expression::process_division_after_polynomial_simplification::collect_rational_expression_monomials_after_denominator_clearing_process;

pub fn objs_equal_by_rational_expression_evaluation(left: &Obj, right: &Obj) -> bool {
    let left_monomials = collect_monomials_in_obj(left);
    let right_monomials = collect_monomials_in_obj(right);

    if monomial_vectors_are_equal(left_monomials.clone(), right_monomials.clone()) {
        return true;
    }

    let (left_monomials_after_denominator_clearing, right_monomials_after_denominator_clearing) =
        collect_rational_expression_monomials_after_denominator_clearing_process(
            left_monomials,
            right_monomials,
        );

    monomial_vectors_are_equal(
        left_monomials_after_denominator_clearing,
        right_monomials_after_denominator_clearing,
    )
}

fn sort_monomials(
    monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
) -> Vec<MonomialWithNonZeroScalarAndOrderedOperands> {
    let mut result = monomials;
    result.sort_by(|a, b| a.key().cmp(&b.key()));
    result
}

fn monomial_vectors_are_equal(
    left_monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
    right_monomials: Vec<MonomialWithNonZeroScalarAndOrderedOperands>,
) -> bool {
    if left_monomials.len() != right_monomials.len() {
        return false;
    }

    let sorted_left = sort_monomials(left_monomials);
    let sorted_right = sort_monomials(right_monomials);

    for (left_monomial, right_monomial) in sorted_left.iter().zip(sorted_right.iter()) {
        if left_monomial.non_zero_scalar != right_monomial.non_zero_scalar {
            return false;
        }
        if left_monomial.key() != right_monomial.key() {
            return false;
        }
    }

    true
}

#[cfg(test)]
mod algebraic_identity_tests {
    use super::*;
    use crate::obj::{Add, Identifier, Mul, Number, Obj, Pow, Sub};

    #[test]
    fn a_plus_b_squared_equals_a_minus_b_squared_plus_4ab() {
        let a = Identifier::mk("a".to_string());
        let b = Identifier::mk("b".to_string());
        let two = Obj::Number(Number::new("2".to_string()));
        let four = Obj::Number(Number::new("4".to_string()));

        let left = Obj::Pow(Pow::new(
            Obj::Add(Add::new(a.clone(), b.clone())),
            two.clone(),
        ));
        let right = Obj::Add(Add::new(
            Obj::Pow(Pow::new(Obj::Sub(Sub::new(a.clone(), b.clone())), two.clone())),
            Obj::Mul(Mul::new(Obj::Mul(Mul::new(four, a.clone())), b.clone())),
        ));

        assert!(objs_equal_by_rational_expression_evaluation(&left, &right));
    }
}
