//! When storing `u = v`, if one side evaluates to a numeric literal and the other is a one-step
//! linear pattern in a single non-constant leaf, also store the solved equality for that leaf.
//!
//! Examples:
//! - `t - 1 = 6` => `t = 7`
//! - `2 * t = 6` => `t = 3` (only if the coefficient literal is provably non-zero; never divide by 0)

use crate::prelude::*;
use crate::verify::{compare_normalized_number_str_to_zero, NumberCompareResult};

fn number_literal_is_nonzero(n: &Number) -> bool {
    !matches!(
        compare_normalized_number_str_to_zero(&n.normalized_value),
        NumberCompareResult::Equal
    )
}

fn obj_is_non_const_leaf_for_solve(x: &Obj) -> bool {
    x.evaluate_to_normalized_decimal_number().is_none()
}

/// Returns a derived [`EqualFact`] with the same `line_file` as `equal`, or `None`.
pub(crate) fn maybe_derived_linear_equal_fact(equal: &EqualFact) -> Option<EqualFact> {
    try_linear_solve_one_side(&equal.left, &equal.right, &equal.line_file)
        .or_else(|| try_linear_solve_one_side(&equal.right, &equal.left, &equal.line_file))
}

fn try_linear_solve_one_side(expr: &Obj, other: &Obj, lf: &LineFile) -> Option<EqualFact> {
    let d = other.evaluate_to_normalized_decimal_number()?;
    let d_obj: Obj = d.clone().into();
    match expr {
        Obj::Sub(s) => {
            let lc = s.left.evaluate_to_normalized_decimal_number();
            let rc = s.right.evaluate_to_normalized_decimal_number();
            match (lc, rc) {
                (None, Some(c_num)) => {
                    let x = s.left.as_ref();
                    if !obj_is_non_const_leaf_for_solve(x) {
                        return None;
                    }
                    let rhs = Obj::Add(Add::new(d_obj, c_num.into()))
                        .evaluate_to_normalized_decimal_number()?;
                    Some(EqualFact::new(x.clone(), rhs.into(), lf.clone()))
                }
                (Some(c_num), None) => {
                    let x = s.right.as_ref();
                    if !obj_is_non_const_leaf_for_solve(x) {
                        return None;
                    }
                    let rhs = Obj::Sub(Sub::new(c_num.into(), d_obj))
                        .evaluate_to_normalized_decimal_number()?;
                    Some(EqualFact::new(x.clone(), rhs.into(), lf.clone()))
                }
                _ => None,
            }
        }
        Obj::Add(a) => {
            let lc = a.left.evaluate_to_normalized_decimal_number();
            let rc = a.right.evaluate_to_normalized_decimal_number();
            match (lc, rc) {
                (None, Some(c_num)) => {
                    let x = a.left.as_ref();
                    if !obj_is_non_const_leaf_for_solve(x) {
                        return None;
                    }
                    let rhs = Obj::Sub(Sub::new(d_obj, c_num.into()))
                        .evaluate_to_normalized_decimal_number()?;
                    Some(EqualFact::new(x.clone(), rhs.into(), lf.clone()))
                }
                (Some(c_num), None) => {
                    let x = a.right.as_ref();
                    if !obj_is_non_const_leaf_for_solve(x) {
                        return None;
                    }
                    let rhs = Obj::Sub(Sub::new(d_obj, c_num.into()))
                        .evaluate_to_normalized_decimal_number()?;
                    Some(EqualFact::new(x.clone(), rhs.into(), lf.clone()))
                }
                _ => None,
            }
        }
        Obj::Mul(m) => {
            let lc = m.left.evaluate_to_normalized_decimal_number();
            let rc = m.right.evaluate_to_normalized_decimal_number();
            match (lc, rc) {
                (Some(c_num), None) => {
                    if !number_literal_is_nonzero(&c_num) {
                        return None;
                    }
                    let x = m.right.as_ref();
                    if !obj_is_non_const_leaf_for_solve(x) {
                        return None;
                    }
                    let rhs = Obj::Div(Div::new(d_obj, c_num.into()))
                        .evaluate_to_normalized_decimal_number()?;
                    Some(EqualFact::new(x.clone(), rhs.into(), lf.clone()))
                }
                (None, Some(c_num)) => {
                    if !number_literal_is_nonzero(&c_num) {
                        return None;
                    }
                    let x = m.left.as_ref();
                    if !obj_is_non_const_leaf_for_solve(x) {
                        return None;
                    }
                    let rhs = Obj::Div(Div::new(d_obj, c_num.into()))
                        .evaluate_to_normalized_decimal_number()?;
                    Some(EqualFact::new(x.clone(), rhs.into(), lf.clone()))
                }
                _ => None,
            }
        }
        Obj::Div(div) => {
            let c = div.right.evaluate_to_normalized_decimal_number()?;
            if !number_literal_is_nonzero(&c) {
                return None;
            }
            let x = div.left.as_ref();
            if !obj_is_non_const_leaf_for_solve(x) {
                return None;
            }
            let rhs = Obj::Mul(Mul::new(d_obj, div.right.as_ref().clone()))
                .evaluate_to_normalized_decimal_number()?;
            Some(EqualFact::new(x.clone(), rhs.into(), lf.clone()))
        }
        _ => None,
    }
}
