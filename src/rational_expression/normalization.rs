use crate::ast::obj::{Obj, ArithmeticOperator};
use crate::rational_expression::decimal_arithmetic::evaluate_obj_to_normalized_decimal_number;
use crate::rational_expression::denominator_clearing::collect_rational_expression_monomials_after_denominator_clearing_process;
use crate::rational_expression::helper::obj_key;
use crate::rational_expression::monomial::MonomialWithNonZeroScalarAndOrderedOperands;
use crate::rational_expression::monomial_collection::collect_monomials_in_obj;
use std::collections::HashSet;

const MAX_DENOMINATOR_CLEARING_ROUNDS: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlgebraicNormalizationMode {
    Ordinary,
    ComplexImaginaryUnit,
}

pub fn objs_equal_by_rational_expression_evaluation(left: &Obj, right: &Obj) -> bool {
    objs_equal_by_algebraic_normalization(left, right, AlgebraicNormalizationMode::Ordinary)
}

// Denominators and negative-power bases that must be nonzero for cancellation
// to be sound. Empty list means a genuine zero-premise identity.
pub fn algebraic_normalization_nonzero_requirements(left: &Obj, right: &Obj) -> Vec<Obj> {
    fn collect(object: &Obj, requirements: &mut Vec<Obj>, seen: &mut HashSet<String>) {
        match object {
            Obj::ArithmeticOperator(ArithmeticOperator::Add(add)) => {
                collect(&add.left, requirements, seen);
                collect(&add.right, requirements, seen);
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Sub(sub)) => {
                collect(&sub.left, requirements, seen);
                collect(&sub.right, requirements, seen);
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Neg(neg)) => {
                collect(&neg.arg, requirements, seen);
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Mul(mul)) => {
                collect(&mul.left, requirements, seen);
                collect(&mul.right, requirements, seen);
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Div(div)) => {
                collect(&div.left, requirements, seen);
                collect(&div.right, requirements, seen);
                let denominator = div.right.as_ref().clone();
                if seen.insert(obj_key(&denominator)) {
                    requirements.push(denominator);
                }
            }
            Obj::ArithmeticOperator(ArithmeticOperator::Pow(pow)) => {
                collect(&pow.base, requirements, seen);
                collect(&pow.exponent, requirements, seen);
                let exponent_is_negative_integer =
                    evaluate_obj_to_normalized_decimal_number(&pow.exponent)
                        .and_then(|number| number.normalized_value.parse::<i128>().ok())
                        .is_some_and(|exponent| exponent < 0);
                if exponent_is_negative_integer {
                    let base = pow.base.as_ref().clone();
                    if seen.insert(obj_key(&base)) {
                        requirements.push(base);
                    }
                }
            }
            _ => {}
        }
    }

    let mut requirements = Vec::new();
    let mut seen = HashSet::new();
    collect(left, &mut requirements, &mut seen);
    collect(right, &mut requirements, &mut seen);
    requirements
}

fn objs_equal_by_algebraic_normalization(
    left: &Obj,
    right: &Obj,
    mode: AlgebraicNormalizationMode,
) -> bool {
    let mut left_monomials = collect_monomials_in_obj(left, mode);
    let mut right_monomials = collect_monomials_in_obj(right, mode);

    for _ in 0..MAX_DENOMINATOR_CLEARING_ROUNDS {
        if monomial_vectors_are_equal(left_monomials.clone(), right_monomials.clone()) {
            return true;
        }

        let previous_left_key = canonical_monomial_vector_key(&left_monomials);
        let previous_right_key = canonical_monomial_vector_key(&right_monomials);
        let (next_left_monomials, next_right_monomials) =
            collect_rational_expression_monomials_after_denominator_clearing_process(
                left_monomials,
                right_monomials,
                mode,
            );
        let next_left_key = canonical_monomial_vector_key(&next_left_monomials);
        let next_right_key = canonical_monomial_vector_key(&next_right_monomials);

        left_monomials = next_left_monomials;
        right_monomials = next_right_monomials;

        if previous_left_key == next_left_key && previous_right_key == next_right_key {
            break;
        }
    }

    monomial_vectors_are_equal(left_monomials, right_monomials)
}

fn canonical_monomial_vector_key(
    monomials: &[MonomialWithNonZeroScalarAndOrderedOperands],
) -> Vec<(String, String)> {
    let mut keys: Vec<(String, String)> = monomials
        .iter()
        .map(|m| (m.key(), m.non_zero_scalar.clone()))
        .collect();
    keys.sort();
    keys
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
