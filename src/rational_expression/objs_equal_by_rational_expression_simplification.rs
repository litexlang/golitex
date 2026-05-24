use crate::prelude::*;
use crate::rational_expression::collect_monomials::collect_monomials_in_obj;
use crate::rational_expression::monomial::MonomialWithNonZeroScalarAndOrderedOperands;
use crate::rational_expression::process_division_after_polynomial_simplification::collect_rational_expression_monomials_after_denominator_clearing_process;

const MAX_DENOMINATOR_CLEARING_ROUNDS: usize = 16;

pub fn objs_equal_by_rational_expression_evaluation(left: &Obj, right: &Obj) -> bool {
    let mut left_monomials = collect_monomials_in_obj(left);
    let mut right_monomials = collect_monomials_in_obj(right);

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
        let pi = Identifier::mk("pi".to_string());
        let one: Obj = Number::new("1".to_string()).into();
        let two: Obj = Number::new("2".to_string()).into();

        let left: Obj = Div::new(
            Sub::new(pi.clone(), Div::new(pi.clone(), two.clone()).into()).into(),
            pi.clone(),
        )
        .into();
        let right: Obj = Sub::new(one.clone(), Div::new(one.clone(), two.clone()).into()).into();
        assert!(objs_equal_by_rational_expression_evaluation(&left, &right));

        let nested_left: Obj =
            Div::new(Div::new(pi.clone(), two.clone()).into(), pi.clone()).into();
        let nested_right: Obj = Div::new(one, two).into();
        assert!(objs_equal_by_rational_expression_evaluation(
            &nested_left,
            &nested_right
        ));
    }
}
