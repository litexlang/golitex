use crate::prelude::*;
use crate::rational_expression::collect_monomials::collect_monomials_in_obj;
use crate::rational_expression::monomial::MonomialWithNonZeroScalarAndOrderedOperands;
use crate::rational_expression::process_division_after_polynomial_simplification::collect_rational_expression_monomials_after_denominator_clearing_process;
use std::collections::HashSet;

const MAX_DENOMINATOR_CLEARING_ROUNDS: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AlgebraicNormalizationMode {
    Ordinary,
    ComplexImaginaryUnit,
}

pub fn objs_equal_by_rational_expression_evaluation(left: &Obj, right: &Obj) -> bool {
    objs_equal_by_algebraic_normalization(left, right, AlgebraicNormalizationMode::Ordinary)
}

/// Proves exact polynomial/rational identities after reducing every pair of
/// imaginary-unit factors by `i * i = -1`.
/// Example: `(1 + i) * (1 - i) = 2`.
pub fn objs_equal_by_complex_rational_expression_evaluation(left: &Obj, right: &Obj) -> bool {
    if !obj_contains_normalizable_imaginary_unit(left)
        && !obj_contains_normalizable_imaginary_unit(right)
    {
        return false;
    }
    objs_equal_by_algebraic_normalization(
        left,
        right,
        AlgebraicNormalizationMode::ComplexImaginaryUnit,
    )
}

/// Returns the ordered, de-duplicated nonzero obligations whose truth makes
/// complex rational normalization sound. Division contributes its
/// denominator, while a negative integral power contributes its base. The
/// verifier freezes proofs of these exact objects into the normalization
/// Result so downstream consumers never have to rediscover them from ambient
/// facts or from a diagnostic label.
pub fn complex_algebraic_normalization_nonzero_requirements(left: &Obj, right: &Obj) -> Vec<Obj> {
    fn collect(object: &Obj, requirements: &mut Vec<Obj>, seen: &mut HashSet<String>) {
        match object {
            Obj::Add(add) => {
                collect(&add.left, requirements, seen);
                collect(&add.right, requirements, seen);
            }
            Obj::Sub(sub) => {
                collect(&sub.left, requirements, seen);
                collect(&sub.right, requirements, seen);
            }
            Obj::Mul(mul) => {
                collect(&mul.left, requirements, seen);
                collect(&mul.right, requirements, seen);
            }
            Obj::Div(div) => {
                collect(&div.left, requirements, seen);
                collect(&div.right, requirements, seen);
                let denominator = div.right.as_ref().clone();
                if seen.insert(obj_equality_key(&denominator)) {
                    requirements.push(denominator);
                }
            }
            Obj::Pow(pow) => {
                collect(&pow.base, requirements, seen);
                collect(&pow.exponent, requirements, seen);
                let exponent_is_negative_integer = pow
                    .exponent
                    .evaluate_to_normalized_decimal_number()
                    .and_then(|number| number.normalized_value.parse::<i128>().ok())
                    .is_some_and(|exponent| exponent < 0);
                if exponent_is_negative_integer {
                    let base = pow.base.as_ref().clone();
                    if seen.insert(obj_equality_key(&base)) {
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

fn obj_contains_normalizable_imaginary_unit(obj: &Obj) -> bool {
    match obj {
        Obj::ImaginaryUnit(_) => true,
        Obj::Add(add) => {
            obj_contains_normalizable_imaginary_unit(&add.left)
                || obj_contains_normalizable_imaginary_unit(&add.right)
        }
        Obj::Sub(sub) => {
            obj_contains_normalizable_imaginary_unit(&sub.left)
                || obj_contains_normalizable_imaginary_unit(&sub.right)
        }
        Obj::Mul(mul) => {
            obj_contains_normalizable_imaginary_unit(&mul.left)
                || obj_contains_normalizable_imaginary_unit(&mul.right)
        }
        Obj::Div(div) => {
            obj_contains_normalizable_imaginary_unit(&div.left)
                || obj_contains_normalizable_imaginary_unit(&div.right)
        }
        Obj::Pow(pow) => {
            obj_contains_normalizable_imaginary_unit(&pow.base)
                || obj_contains_normalizable_imaginary_unit(&pow.exponent)
        }
        _ => false,
    }
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

#[cfg(test)]
mod algebraic_identity_tests {
    use super::*;

    #[test]
    fn a_plus_b_squared_equals_a_minus_b_squared_plus_4ab() {
        let a = Identifier::mk("a".to_string());
        let b = Identifier::mk("b".to_string());
        let two: Obj = Number::new("2".to_string()).into();
        let four: Obj = Number::new("4".to_string()).into();

        let left = Pow::new(Add::new(a.clone(), b.clone()).into(), two.clone()).into();
        let right = Add::new(
            Pow::new(Sub::new(a.clone(), b.clone()).into(), two.clone()).into(),
            Mul::new(Mul::new(four, a.clone()).into(), b.clone()).into(),
        )
        .into();

        assert!(objs_equal_by_rational_expression_evaluation(&left, &right));
    }

    #[test]
    fn two_an_plus_bm_squared_equals_expanded_rhs() {
        use crate::parse::{TokenBlock, Tokenizer};
        use crate::runtime::Runtime;
        use std::rc::Rc;

        fn parse_obj_line(line: &str) -> Obj {
            let tokenizer = Tokenizer::new();
            let line_file = (1, Rc::from("test.lit"));
            let tokens = tokenizer.tokenize_line(line, line_file.clone()).unwrap();
            let mut tb = TokenBlock::new(tokens, vec![], line_file);
            let mut rt = Runtime::new();
            rt.parse_obj(&mut tb).expect("parse")
        }

        let left = parse_obj_line(r#"( 2 * a * n + b * m ) ^ 2"#);
        let right = parse_obj_line(
            r#"2 * ( a * m + b * n ) ^ 2 + ( m ^ 2 - 2 * n ^ 2 ) * ( b ^ 2 - 2 * a ^ 2 )"#,
        );
        assert!(objs_equal_by_rational_expression_evaluation(&left, &right));
    }

    #[test]
    fn nested_divisions_reach_denominator_clearing_fixed_point() {
        let x = Identifier::mk("x".to_string());
        let one: Obj = Number::new("1".to_string()).into();
        let two: Obj = Number::new("2".to_string()).into();

        let left: Obj = Div::new(
            Sub::new(x.clone(), Div::new(x.clone(), two.clone()).into()).into(),
            x.clone(),
        )
        .into();
        let right: Obj = Sub::new(one.clone(), Div::new(one.clone(), two.clone()).into()).into();
        assert!(objs_equal_by_rational_expression_evaluation(&left, &right));

        let nested_left: Obj = Div::new(Div::new(x.clone(), two.clone()).into(), x.clone()).into();
        let nested_right: Obj = Div::new(one, two).into();
        assert!(objs_equal_by_rational_expression_evaluation(
            &nested_left,
            &nested_right
        ));
    }

    #[test]
    fn complex_mode_reduces_imaginary_unit_products() {
        let i: Obj = ImaginaryUnit::new().into();
        let one: Obj = Number::new("1".to_string()).into();
        let two: Obj = Number::new("2".to_string()).into();

        let left: Obj = Add::new(Mul::new(two.clone(), i.clone()).into(), one.clone()).into();
        let right: Obj = Add::new(
            Add::new(Mul::new(i.clone(), i.clone()).into(), two.clone()).into(),
            Mul::new(two, i.clone()).into(),
        )
        .into();
        assert!(objs_equal_by_complex_rational_expression_evaluation(
            &left, &right
        ));

        let wrong: Obj = Number::new("1".to_string()).into();
        assert!(!objs_equal_by_complex_rational_expression_evaluation(
            &Mul::new(i.clone(), i).into(),
            &wrong,
        ));
    }

    #[test]
    fn complex_mode_clears_imaginary_denominators() {
        let i: Obj = ImaginaryUnit::new().into();
        let one: Obj = Number::new("1".to_string()).into();
        let minus_one: Obj = Number::new("-1".to_string()).into();
        let left: Obj = Div::new(one, i.clone()).into();
        let right: Obj = Mul::new(minus_one, i).into();

        assert!(objs_equal_by_complex_rational_expression_evaluation(
            &left, &right
        ));
    }
}
