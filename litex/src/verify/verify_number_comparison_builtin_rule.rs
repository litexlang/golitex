use crate::fact::AtomicFact;
use crate::obj::Obj;

enum NumberCompareResult {
    Less,
    Equal,
    Greater,
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

fn compare_number_strings(
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

fn calculate_obj_pair_to_number_strings(
    left_obj: &Obj,
    right_obj: &Obj,
) -> Option<(String, String)> {
    if !left_obj.can_be_calculated() || !right_obj.can_be_calculated() {
        return None;
    }
    Some((
        left_obj.calculate_to_string(),
        right_obj.calculate_to_string(),
    ))
}

pub fn verify_number_comparison_builtin_rule(atomic_fact: &AtomicFact) -> Option<bool> {
    match atomic_fact {
        AtomicFact::LessFact(less_fact) => {
            let calculated_number_string_pair =
                calculate_obj_pair_to_number_strings(&less_fact.left, &less_fact.right)?;
            Some(matches!(
                compare_number_strings(
                    &calculated_number_string_pair.0,
                    &calculated_number_string_pair.1
                ),
                NumberCompareResult::Less
            ))
        }
        AtomicFact::GreaterFact(greater_fact) => {
            let calculated_number_string_pair =
                calculate_obj_pair_to_number_strings(&greater_fact.left, &greater_fact.right)?;
            Some(matches!(
                compare_number_strings(
                    &calculated_number_string_pair.0,
                    &calculated_number_string_pair.1
                ),
                NumberCompareResult::Greater
            ))
        }
        AtomicFact::LessEqualFact(less_equal_fact) => {
            let calculated_number_string_pair = calculate_obj_pair_to_number_strings(
                &less_equal_fact.left,
                &less_equal_fact.right,
            )?;
            let compare_result = compare_number_strings(
                &calculated_number_string_pair.0,
                &calculated_number_string_pair.1,
            );
            Some(matches!(
                compare_result,
                NumberCompareResult::Less | NumberCompareResult::Equal
            ))
        }
        AtomicFact::GreaterEqualFact(greater_equal_fact) => {
            let calculated_number_string_pair = calculate_obj_pair_to_number_strings(
                &greater_equal_fact.left,
                &greater_equal_fact.right,
            )?;
            let compare_result = compare_number_strings(
                &calculated_number_string_pair.0,
                &calculated_number_string_pair.1,
            );
            Some(matches!(
                compare_result,
                NumberCompareResult::Greater | NumberCompareResult::Equal
            ))
        }
        AtomicFact::NotLessFact(not_less_fact) => {
            let calculated_number_string_pair =
                calculate_obj_pair_to_number_strings(&not_less_fact.left, &not_less_fact.right)?;
            let compare_result = compare_number_strings(
                &calculated_number_string_pair.0,
                &calculated_number_string_pair.1,
            );
            Some(matches!(
                compare_result,
                NumberCompareResult::Greater | NumberCompareResult::Equal
            ))
        }
        AtomicFact::NotGreaterFact(not_greater_fact) => {
            let calculated_number_string_pair = calculate_obj_pair_to_number_strings(
                &not_greater_fact.left,
                &not_greater_fact.right,
            )?;
            let compare_result = compare_number_strings(
                &calculated_number_string_pair.0,
                &calculated_number_string_pair.1,
            );
            Some(matches!(
                compare_result,
                NumberCompareResult::Less | NumberCompareResult::Equal
            ))
        }
        AtomicFact::NotLessEqualFact(not_less_equal_fact) => {
            let calculated_number_string_pair = calculate_obj_pair_to_number_strings(
                &not_less_equal_fact.left,
                &not_less_equal_fact.right,
            )?;
            Some(matches!(
                compare_number_strings(
                    &calculated_number_string_pair.0,
                    &calculated_number_string_pair.1
                ),
                NumberCompareResult::Greater
            ))
        }
        AtomicFact::NotGreaterEqualFact(not_greater_equal_fact) => {
            let calculated_number_string_pair = calculate_obj_pair_to_number_strings(
                &not_greater_equal_fact.left,
                &not_greater_equal_fact.right,
            )?;
            Some(matches!(
                compare_number_strings(
                    &calculated_number_string_pair.0,
                    &calculated_number_string_pair.1
                ),
                NumberCompareResult::Less
            ))
        }
        _ => None,
    }
}
