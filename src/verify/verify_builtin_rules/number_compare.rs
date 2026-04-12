use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;

pub(crate) enum NumberCompareResult {
    Less,
    Equal,
    Greater,
}

/// Compare a normalized decimal string (same shape as [`Number::normalized_value`]) to `"0"`.
pub(crate) fn compare_normalized_number_str_to_zero(number_value: &str) -> NumberCompareResult {
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

pub(crate) fn compare_number_strings(
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

impl Runtime {
    pub(crate) fn verify_order_atomic_fact_numeric_builtin_only(
        &self,
        atomic_fact: &AtomicFact,
    ) -> StmtExecResult {
        if let AtomicFact::LessEqualFact(less_equal_fact) = atomic_fact {
            if less_equal_fact.left.to_string() == less_equal_fact.right.to_string() {
                return StmtExecResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        Fact::AtomicFact(AtomicFact::LessEqualFact(less_equal_fact.clone())),
                        "less_equal_fact_equal".to_string(),
                        Vec::new(),
                    ),
                );
            }
            let strict_fact = Fact::AtomicFact(AtomicFact::LessFact(LessFact::new(
                less_equal_fact.left.clone(),
                less_equal_fact.right.clone(),
                less_equal_fact.line_file.clone(),
            )));
            let strict_key = strict_fact.to_string();
            let (cache_ok, cache_line_file) = self.cache_known_facts_contains(&strict_key);
            if cache_ok {
                return StmtExecResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_known_fact_source_recording_facts(
                        Fact::AtomicFact(AtomicFact::LessEqualFact(less_equal_fact.clone())),
                        strict_key,
                        Some(strict_fact),
                        Some(cache_line_file),
                        Vec::new(),
                    ),
                );
            }
        }
        if let AtomicFact::GreaterEqualFact(greater_equal_fact) = atomic_fact {
            if greater_equal_fact.left.to_string() == greater_equal_fact.right.to_string() {
                return StmtExecResult::FactualStmtSuccess(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        Fact::AtomicFact(AtomicFact::GreaterEqualFact(greater_equal_fact.clone())),
                        "greater_equal_fact_equal".to_string(),
                        Vec::new(),
                    ),
                );
            }
        }
        if let Some(true) = self.verify_number_comparison_builtin_rule(atomic_fact) {
            StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(atomic_fact.clone()),
                    "number comparison".to_string(),
                    Vec::new(),
                ),
            )
        } else {
            StmtExecResult::StmtUnknown(StmtUnknown::new())
        }
    }

    pub fn verify_number_comparison_builtin_rule(&self, atomic_fact: &AtomicFact) -> Option<bool> {
        let normalized = normalize_positive_order_atomic_fact(atomic_fact)?;
        match normalized {
            AtomicFact::LessFact(less_fact) => {
                if let Some(calculated_number_string_pair) =
                    self.calculate_obj_pair_to_number_strings(&less_fact.left, &less_fact.right)
                {
                    return Some(matches!(
                        compare_number_strings(
                            &calculated_number_string_pair.0,
                            &calculated_number_string_pair.1
                        ),
                        NumberCompareResult::Less
                    ));
                }
                self.try_verify_numeric_order_via_div_elimination(
                    &less_fact.left,
                    &less_fact.right,
                    false,
                )
            }
            AtomicFact::LessEqualFact(less_equal_fact) => {
                if let Some(calculated_number_string_pair) = self.calculate_obj_pair_to_number_strings(
                    &less_equal_fact.left,
                    &less_equal_fact.right,
                ) {
                    let compare_result = compare_number_strings(
                        &calculated_number_string_pair.0,
                        &calculated_number_string_pair.1,
                    );
                    return Some(matches!(
                        compare_result,
                        NumberCompareResult::Less | NumberCompareResult::Equal
                    ));
                }
                self.try_verify_numeric_order_via_div_elimination(
                    &less_equal_fact.left,
                    &less_equal_fact.right,
                    true,
                )
            }
            _ => None,
        }
    }

    fn calculate_obj_pair_to_number_strings(
        &self,
        left_obj: &Obj,
        right_obj: &Obj,
    ) -> Option<(String, String)> {
        let left_number = self.resolve_obj_to_number_resolved(left_obj)?;
        let right_number = self.resolve_obj_to_number_resolved(right_obj)?;
        Some((left_number.normalized_value, right_number.normalized_value))
    }
}
