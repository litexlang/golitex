//! Exact comparison of normalized decimal strings.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NumberCompareResult {
    Less,
    Equal,
    Greater,
}

// Compare a normalized decimal string to "0".
pub fn compare_normalized_number_str_to_zero(number_value: &str) -> NumberCompareResult {
    compare_number_strings(number_value.trim(), "0")
}

fn parse_number_parts_for_comparison(number_value: &str) -> (bool, Vec<u8>, Vec<u8>) {
    let trimmed_number_value = number_value.trim();
    let (is_negative, magnitude_string) = if trimmed_number_value.starts_with('-') {
        (true, trimmed_number_value[1..].trim())
    } else {
        (false, trimmed_number_value)
    };

    let (integer_part_string, fractional_part_string) = match magnitude_string.find('.') {
        Some(dot_index) => (
            &magnitude_string[..dot_index],
            &magnitude_string[dot_index + 1..],
        ),
        None => (magnitude_string, ""),
    };

    let mut integer_digits: Vec<u8> = Vec::new();
    if integer_part_string.is_empty() {
        integer_digits.push(0);
    } else {
        for current_char in integer_part_string.chars() {
            if current_char.is_ascii_digit() {
                integer_digits.push(current_char as u8 - b'0');
            }
        }
        if integer_digits.is_empty() {
            integer_digits.push(0);
        }
    }

    let mut fractional_digits: Vec<u8> = Vec::new();
    for current_char in fractional_part_string.chars() {
        if current_char.is_ascii_digit() {
            fractional_digits.push(current_char as u8 - b'0');
        }
    }

    (is_negative, integer_digits, fractional_digits)
}

fn digits_are_all_zero(digits: &[u8]) -> bool {
    for digit in digits {
        if *digit != 0 {
            return false;
        }
    }
    true
}

fn normalized_decimal_string_is_integer(number_value: &str) -> bool {
    let (_, _integer_digits, fractional_digits) = parse_number_parts_for_comparison(number_value);
    digits_are_all_zero(&fractional_digits)
}

pub fn normalized_decimal_string_is_even_integer(number_value: &str) -> bool {
    if !normalized_decimal_string_is_integer(number_value) {
        return false;
    }
    let (_is_negative, integer_digits, _fractional_digits) =
        parse_number_parts_for_comparison(number_value);
    let last_digit = integer_digits.last().copied().unwrap_or(0);
    last_digit % 2 == 0
}

fn first_non_zero_integer_digit_index(integer_digits: &[u8]) -> usize {
    let mut current_index = 0;
    while current_index + 1 < integer_digits.len() && integer_digits[current_index] == 0 {
        current_index += 1;
    }
    current_index
}

fn compare_non_negative_decimal_parts(
    left_integer_digits: &[u8],
    left_fractional_digits: &[u8],
    right_integer_digits: &[u8],
    right_fractional_digits: &[u8],
) -> NumberCompareResult {
    let left_integer_start_index = first_non_zero_integer_digit_index(left_integer_digits);
    let right_integer_start_index = first_non_zero_integer_digit_index(right_integer_digits);

    let left_effective_integer_len = left_integer_digits.len() - left_integer_start_index;
    let right_effective_integer_len = right_integer_digits.len() - right_integer_start_index;
    if left_effective_integer_len < right_effective_integer_len {
        return NumberCompareResult::Less;
    }
    if left_effective_integer_len > right_effective_integer_len {
        return NumberCompareResult::Greater;
    }

    let mut integer_index = 0;
    while integer_index < left_effective_integer_len {
        let left_digit = left_integer_digits[left_integer_start_index + integer_index];
        let right_digit = right_integer_digits[right_integer_start_index + integer_index];
        if left_digit < right_digit {
            return NumberCompareResult::Less;
        }
        if left_digit > right_digit {
            return NumberCompareResult::Greater;
        }
        integer_index += 1;
    }

    let fractional_compare_len = if left_fractional_digits.len() > right_fractional_digits.len() {
        left_fractional_digits.len()
    } else {
        right_fractional_digits.len()
    };
    let mut fractional_index = 0;
    while fractional_index < fractional_compare_len {
        let left_digit = match left_fractional_digits.get(fractional_index) {
            Some(digit) => *digit,
            None => 0,
        };
        let right_digit = match right_fractional_digits.get(fractional_index) {
            Some(digit) => *digit,
            None => 0,
        };
        if left_digit < right_digit {
            return NumberCompareResult::Less;
        }
        if left_digit > right_digit {
            return NumberCompareResult::Greater;
        }
        fractional_index += 1;
    }

    NumberCompareResult::Equal
}

pub fn compare_number_strings(
    left_number_value: &str,
    right_number_value: &str,
) -> NumberCompareResult {
    let (left_is_negative, left_integer_digits, left_fractional_digits) =
        parse_number_parts_for_comparison(left_number_value);
    let (right_is_negative, right_integer_digits, right_fractional_digits) =
        parse_number_parts_for_comparison(right_number_value);

    let left_is_zero =
        digits_are_all_zero(&left_integer_digits) && digits_are_all_zero(&left_fractional_digits);
    let right_is_zero =
        digits_are_all_zero(&right_integer_digits) && digits_are_all_zero(&right_fractional_digits);
    if left_is_zero && right_is_zero {
        return NumberCompareResult::Equal;
    }

    if left_is_negative && !left_is_zero && !right_is_negative {
        return NumberCompareResult::Less;
    }
    if right_is_negative && !right_is_zero && !left_is_negative {
        return NumberCompareResult::Greater;
    }

    let non_negative_compare_result = compare_non_negative_decimal_parts(
        &left_integer_digits,
        &left_fractional_digits,
        &right_integer_digits,
        &right_fractional_digits,
    );
    if left_is_negative && !left_is_zero && right_is_negative && !right_is_zero {
        return match non_negative_compare_result {
            NumberCompareResult::Less => NumberCompareResult::Greater,
            NumberCompareResult::Equal => NumberCompareResult::Equal,
            NumberCompareResult::Greater => NumberCompareResult::Less,
        };
    }

    non_negative_compare_result
}

use crate::ast::obj::Obj;
use crate::rational_expression::evaluate_obj_to_normalized_decimal_number;

// Compare closed numeric values exactly, preserving the decimal fast path.
// Returns (cmp, left_normal, right_normal).
// Example: `1 + 1` vs `3` → (Less, "2", "3").
pub fn compare_closed_numeric_objs(
    left: &Obj,
    right: &Obj,
) -> Option<(NumberCompareResult, String, String)> {
    if let (Some(left_number), Some(right_number)) = (
        evaluate_obj_to_normalized_decimal_number(left),
        evaluate_obj_to_normalized_decimal_number(right),
    ) {
        let cmp = compare_number_strings(&left_number.normalized_value, &right_number.normalized_value);
        return Some((cmp, left_number.normalized_value, right_number.normalized_value));
    }
    // Positive normalized denominators make checked cross-products sound.
    // Example: 1/3 < 1/2; no float or rounded decimal participates.
    let left = super::exact_rational::EvalRational::from_obj(left)?;
    let right = super::exact_rational::EvalRational::from_obj(right)?;
    Some((
        left.compare(&right)?,
        left.to_obj().readable_string(),
        right.to_obj().readable_string(),
    ))
}
