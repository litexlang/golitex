use crate::prelude::*;
use crate::rational_expression::mul_signed_decimal_str;

use super::number_compare::{compare_number_strings, NumberCompareResult};

fn decimal_str_sign_vs_zero(number_value: &str) -> NumberCompareResult {
    compare_number_strings(number_value.trim(), "0")
}

// None if denominator is zero; Some(false) positive; Some(true) negative (flip inequality).
fn nonzero_denominator_requires_flip(denominator_normalized: &str) -> Option<bool> {
    match decimal_str_sign_vs_zero(denominator_normalized) {
        NumberCompareResult::Equal => None,
        NumberCompareResult::Greater => Some(false),
        NumberCompareResult::Less => Some(true),
    }
}

// None if either denominator is zero; Some(true) if v*y > 0; Some(false) if v*y < 0.
fn two_denominators_product_is_positive(left_den: &str, right_den: &str) -> Option<bool> {
    let l = decimal_str_sign_vs_zero(left_den);
    let r = decimal_str_sign_vs_zero(right_den);
    match (l, r) {
        (NumberCompareResult::Equal, _) | (_, NumberCompareResult::Equal) => None,
        (NumberCompareResult::Less, NumberCompareResult::Less)
        | (NumberCompareResult::Greater, NumberCompareResult::Greater) => Some(true),
        _ => Some(false),
    }
}

fn compare_result_matches_less_order(
    compare_result: NumberCompareResult,
    allow_equal: bool,
    flip: bool,
) -> bool {
    if !flip {
        if allow_equal {
            matches!(
                compare_result,
                NumberCompareResult::Less | NumberCompareResult::Equal
            )
        } else {
            matches!(compare_result, NumberCompareResult::Less)
        }
    } else if allow_equal {
        matches!(
            compare_result,
            NumberCompareResult::Greater | NumberCompareResult::Equal
        )
    } else {
        matches!(compare_result, NumberCompareResult::Greater)
    }
}

impl Runtime {
    pub(crate) fn try_verify_numeric_order_via_div_elimination(
        &self,
        left_obj: &Obj,
        right_obj: &Obj,
        allow_equal: bool,
    ) -> Option<bool> {
        if let (Obj::Div(left_div), Obj::Div(right_div)) = (left_obj, right_obj) {
            let left_denominator_number = self.resolve_obj_to_number_resolved(&left_div.right)?;
            let right_denominator_number = self.resolve_obj_to_number_resolved(&right_div.right)?;
            let left_den_str = left_denominator_number.normalized_value.as_str();
            let right_den_str = right_denominator_number.normalized_value.as_str();
            let product_positive = two_denominators_product_is_positive(left_den_str, right_den_str)?;
            let flip = !product_positive;
            let left_numerator_number = self.resolve_obj_to_number_resolved(&left_div.left)?;
            let right_numerator_number = self.resolve_obj_to_number_resolved(&right_div.left)?;
            let left_product = mul_signed_decimal_str(
                &left_numerator_number.normalized_value,
                &right_denominator_number.normalized_value,
            );
            let right_product = mul_signed_decimal_str(
                &right_numerator_number.normalized_value,
                &left_denominator_number.normalized_value,
            );
            let compare_result = compare_number_strings(&left_product, &right_product);
            return Some(compare_result_matches_less_order(
                compare_result,
                allow_equal,
                flip,
            ));
        }

        if let Obj::Div(right_div) = right_obj {
            let denominator_number = self.resolve_obj_to_number_resolved(&right_div.right)?;
            let flip = nonzero_denominator_requires_flip(&denominator_number.normalized_value)?;
            let numerator_number = self.resolve_obj_to_number_resolved(&right_div.left)?;
            let left_number = self.resolve_obj_to_number_resolved(left_obj)?;
            let left_scaled = mul_signed_decimal_str(
                &left_number.normalized_value,
                &denominator_number.normalized_value,
            );
            let compare_result =
                compare_number_strings(&left_scaled, &numerator_number.normalized_value);
            return Some(compare_result_matches_less_order(
                compare_result,
                allow_equal,
                flip,
            ));
        }

        if let Obj::Div(left_div) = left_obj {
            let denominator_number = self.resolve_obj_to_number_resolved(&left_div.right)?;
            let flip = nonzero_denominator_requires_flip(&denominator_number.normalized_value)?;
            let numerator_number = self.resolve_obj_to_number_resolved(&left_div.left)?;
            let right_number = self.resolve_obj_to_number_resolved(right_obj)?;
            let right_scaled = mul_signed_decimal_str(
                &right_number.normalized_value,
                &denominator_number.normalized_value,
            );
            let compare_result =
                compare_number_strings(&numerator_number.normalized_value, &right_scaled);
            return Some(compare_result_matches_less_order(
                compare_result,
                allow_equal,
                flip,
            ));
        }

        None
    }
}
