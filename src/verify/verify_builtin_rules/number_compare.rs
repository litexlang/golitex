use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;

impl Runtime {
    // Lit `trust` facts for the nonnegative / positive cone under field operations used to live in
    // `BUILTIN_ENV_CODE_FOR_FUNDAMENTAL_COMPARISON` (`fundamental_comparison.rs`). Those fragments
    // were removed as redundant; the same mathematics is checked here on normalized `0 <=` / `0 <`
    // goals (possibly after `normalize_positive_order_atomic_fact`):
    // - Chained `+`: `0 <= a + b + …` from `0 <=` on each peeled summand; `0 < a + b + …` from
    //   `(0 < a ∧ 0 <= b) ∨ (0 <= a ∧ 0 < b)` at each binary `+`.
    // - Powers: literal even integer exponent ⇒ `0 <= base^n`; literal integer exponent and `0 <= base`
    //   (or `0 < base` if exponent < 0) ⇒ `0 <= base^n`; `a * a` with equal factors; `0 < base^exp`
    //   from `0 < base` and `exp in R`.
    // - Products and quotients: `0 <= a * b`, `0 < a * b`, `0 <= a / b` (denominator strictly
    //   positive), `0 < a / b`, each with recursive sub-goals on operands.
    // The Lit environment still records order via differences (`a <= b` iff `0 <= b - a`, etc.) and
    // `a != 0 ⇒ 0 < a^2` (strict square). This path also bridges `0 <= u - v` / `0 < u - v` to `v <= u` / `v < u`.
    // Algebraic closure (+, -, *, /) on general `a <= b` / `a < b` is in `order_algebra_builtin.rs`.
    pub fn verify_order_atomic_fact_numeric_builtin_only(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let vs = VerifyState::new(0, true);
        if let Some(result) =
            self.try_verify_finite_nonempty_set_size_at_least_one(atomic_fact, &vs)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_order_nonnegative_from_membership_in_n(atomic_fact, &vs)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_order_one_le_from_membership_in_n_pos(atomic_fact, &vs)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_order_one_le_from_membership_in_n_and_nonzero(atomic_fact, &vs)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_order_one_le_from_membership_in_z_and_positive(atomic_fact, &vs)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_numeric_lower_bound_from_known_lower_bound(atomic_fact, &vs)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_numeric_upper_bound_from_known_upper_bound(atomic_fact, &vs)?
        {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_mod_remainder_bounds(atomic_fact, &vs)? {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_order_opposite_sign_mul_minus_one(atomic_fact, &vs)? {
            return Ok(result);
        }
        if let Some(result) = self.verify_order_from_known_negated_complement(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) = self.verify_negated_order_from_known_equivalent_order(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) = self.verify_order_algebra_structural_builtin_rule(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) = self.verify_zero_le_abs_builtin_rule(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_le_sqrt_from_nonnegative_arg_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_lt_sqrt_from_positive_arg_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) = self.verify_sqrt_monotonicity_builtin_rule(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) = self.verify_log_order_builtin_rule(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) = self.verify_abs_order_builtin_rule(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) = self.verify_abs_order_strict_builtin_rule(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_order_on_sub_from_two_sided_order_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_le_add_from_known_atomic_facts_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_lt_add_from_known_atomic_facts_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) = self.verify_zero_le_even_integer_pow_builtin_rule(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_lt_even_integer_pow_from_base_nonzero_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_lt_pow_from_positive_base_real_exp_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_le_pow_from_positive_base_real_exp_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) = self
            .verify_zero_le_pow_from_nonnegative_base_positive_integer_exp_builtin_rule(
                atomic_fact,
            )?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_le_pow_integer_exponent_from_nonneg_base_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_le_mul_from_known_atomic_facts_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_lt_mul_from_known_atomic_facts_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_le_div_from_known_atomic_facts_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_lt_div_from_known_atomic_facts_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }

        if let AtomicFact::LessEqualFact(less_equal_fact) = atomic_fact {
            if less_equal_fact.left.to_string() == less_equal_fact.right.to_string() {
                return Ok(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        less_equal_fact.clone().into(),
                        "less_equal_fact_equal".to_string(),
                        Vec::new(),
                    ),
                ));
            }
            let equal_result = self.verify_objs_are_equal_known_only(
                &less_equal_fact.left,
                &less_equal_fact.right,
                less_equal_fact.line_file.clone(),
            );
            if equal_result.is_true() {
                return Ok(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        less_equal_fact.clone().into(),
                        "less_equal_fact_from_known_equality".to_string(),
                        vec![equal_result],
                    ),
                ));
            }
            let strict_atomic: AtomicFact = LessFact::new(
                less_equal_fact.left.clone(),
                less_equal_fact.right.clone(),
                less_equal_fact.line_file.clone(),
            )
            .into();
            let strict_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&strict_atomic)?;
            if strict_result.is_true() {
                return Ok(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        less_equal_fact.clone().into(),
                        "less_equal_fact_from_known_strict_order".to_string(),
                        vec![strict_result],
                    ),
                ));
            }
        }
        if let AtomicFact::GreaterEqualFact(greater_equal_fact) = atomic_fact {
            if greater_equal_fact.left.to_string() == greater_equal_fact.right.to_string() {
                return Ok(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        greater_equal_fact.clone().into(),
                        "greater_equal_fact_equal".to_string(),
                        Vec::new(),
                    ),
                ));
            }
            let equal_result = self.verify_objs_are_equal_known_only(
                &greater_equal_fact.left,
                &greater_equal_fact.right,
                greater_equal_fact.line_file.clone(),
            );
            if equal_result.is_true() {
                return Ok(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        greater_equal_fact.clone().into(),
                        "greater_equal_fact_from_known_equality".to_string(),
                        vec![equal_result],
                    ),
                ));
            }

            // Strict order implies weak order. Example: from `pi > 0`, prove `pi >= 0`.
            let strict_atomic: AtomicFact = GreaterFact::new(
                greater_equal_fact.left.clone(),
                greater_equal_fact.right.clone(),
                greater_equal_fact.line_file.clone(),
            )
            .into();
            let strict_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&strict_atomic)?;
            if strict_result.is_true() {
                return Ok(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        greater_equal_fact.clone().into(),
                        "greater_equal_fact_from_known_strict_order".to_string(),
                        vec![strict_result],
                    ),
                ));
            }
        }
        if let Some(true) = self.verify_number_comparison_builtin_rule(atomic_fact) {
            Ok(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "number comparison".to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtResult::Unknown(StmtUnknown::new()))
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
                if let Some(calculated_number_string_pair) = self
                    .calculate_obj_pair_to_number_strings(
                        &less_equal_fact.left,
                        &less_equal_fact.right,
                    )
                {
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
}

pub enum NumberCompareResult {
    Less,
    Equal,
    Greater,
}

/// Compare a normalized decimal string (same shape as [`Number::normalized_value`]) to `"0"`.
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

pub(crate) fn normalized_decimal_string_is_even_integer(number_value: &str) -> bool {
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

impl Runtime {
    /// Sub-goals inside numeric builtins: known env + builtin rules only.
    /// Do not call [`Runtime::verify_non_equational_atomic_fact`] here: its forall / definition
    /// round can recurse with outer goals (e.g. `b in R` for `0 <= a^b`, or order lemmas).
    pub(crate) fn verify_non_equational_known_then_builtin_rules_only(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let r = self.verify_non_equational_atomic_fact_with_known_atomic_facts(atomic_fact)?;
        if r.is_true() {
            return Ok(r);
        }
        self.verify_non_equational_atomic_fact_with_restricted_builtin_rules(
            atomic_fact,
            verify_state,
        )
    }

    fn verify_zero_order_on_sub_expr(
        &mut self,
        zero: &Obj,
        sub_expr: &Obj,
        weak: bool,
        line_file: &LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        let fact: AtomicFact = if weak {
            LessEqualFact::new(zero.clone(), sub_expr.clone(), line_file.clone()).into()
        } else {
            LessFact::new(zero.clone(), sub_expr.clone(), line_file.clone()).into()
        };
        let mut result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&fact)?;
        if !result.is_true() {
            result = self.verify_order_atomic_fact_numeric_builtin_only(&fact)?;
        }
        Ok(result)
    }

    /// `n >= 0` / `0 <= n` from known `n $in N` (e.g. `forall n N:` domain).
    fn try_verify_order_nonnegative_from_membership_in_n(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (n, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(z) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_normalized_number_str_to_zero(&z.normalized_value),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(z) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_normalized_number_str_to_zero(&z.normalized_value),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let in_n: AtomicFact = InFact::new(n, StandardSet::N.into(), line_file.clone()).into();
        if self
            .verify_non_equational_known_then_builtin_rules_only(&in_n, verify_state)?
            .is_true()
        {
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "n >= 0 from n $in N".to_string(),
                    Vec::new(),
                ),
            )));
        }
        Ok(None)
    }

    /// `n >= 1` / `1 <= n` from known `n $in N_pos`.
    fn try_verify_order_one_le_from_membership_in_n_pos(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (n, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let in_n_pos: AtomicFact =
            InFact::new(n, StandardSet::NPos.into(), line_file.clone()).into();
        if self
            .verify_non_equational_known_then_builtin_rules_only(&in_n_pos, verify_state)?
            .is_true()
        {
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "n >= 1 from n $in N_pos".to_string(),
                    Vec::new(),
                ),
            )));
        }
        Ok(None)
    }

    // A nonempty finite set has at least one element.
    // Example: `$is_finite_set(S)`, `$is_nonempty_set(S)` => `finite_set_size(S) >= 1`.
    fn try_verify_finite_nonempty_set_size_at_least_one(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (finite_set_size_obj, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(right) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&right.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(left) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&left.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let Obj::FiniteSetSize(finite_set_size) = finite_set_size_obj else {
            return Ok(None);
        };
        let set = (*finite_set_size.set).clone();

        let finite: AtomicFact = IsFiniteSetFact::new(set.clone(), line_file.clone()).into();
        let finite_result =
            self.verify_non_equational_known_then_builtin_rules_only(&finite, verify_state)?;
        if !finite_result.is_true() {
            return Ok(None);
        }

        let nonempty: AtomicFact = IsNonemptySetFact::new(set, line_file).into();
        let nonempty_result =
            self.verify_non_equational_known_then_builtin_rules_only(&nonempty, verify_state)?;
        if !nonempty_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                atomic_fact.clone().into(),
                InferResult::new(),
                "finite_nonempty_set_size_at_least_one".to_string(),
                vec![finite_result, nonempty_result],
            )
            .into(),
        ))
    }

    /// `n >= 1` / `1 <= n` from known `n $in N` and `n != 0` (nonzero naturals are at least 1).
    /// Example: `forall x N: x != 0 =>: 1 <= x`.
    fn try_verify_order_one_le_from_membership_in_n_and_nonzero(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (n, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let in_n: AtomicFact =
            InFact::new(n.clone(), StandardSet::N.into(), line_file.clone()).into();
        let nonzero: AtomicFact = NotEqualFact::new(n, zero_obj, line_file.clone()).into();
        if !self
            .verify_non_equational_known_then_builtin_rules_only(&in_n, verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&nonzero)?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "1 <= n from n $in N and n != 0".to_string(),
                Vec::new(),
            ),
        )))
    }

    /// Euclidean remainders modulo a positive integer lie in the standard interval.
    /// Example: from `a $in Z` and `b $in N_pos`, prove `0 <= a % b < b`.
    fn try_verify_mod_remainder_bounds(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let (mod_obj, line_file, strict_upper_bound) = match &norm {
            AtomicFact::LessEqualFact(f) => {
                let Some(zero) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_normalized_number_str_to_zero(&zero.normalized_value),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                let Obj::Mod(m) = &f.right else {
                    return Ok(None);
                };
                (m, f.line_file.clone(), false)
            }
            AtomicFact::LessFact(f) => {
                let Obj::Mod(m) = &f.left else {
                    return Ok(None);
                };
                if m.right.to_string() != f.right.to_string() {
                    return Ok(None);
                }
                (m, f.line_file.clone(), true)
            }
            _ => return Ok(None),
        };

        let dividend_in_z: AtomicFact = InFact::new(
            mod_obj.left.as_ref().clone(),
            StandardSet::Z.into(),
            line_file.clone(),
        )
        .into();
        let dividend_result =
            self.verify_non_equational_known_then_builtin_rules_only(&dividend_in_z, verify_state)?;
        if !dividend_result.is_true() {
            return Ok(None);
        }

        let modulus_in_n_pos: AtomicFact = InFact::new(
            mod_obj.right.as_ref().clone(),
            StandardSet::NPos.into(),
            line_file,
        )
        .into();
        let modulus_result = self
            .verify_non_equational_known_then_builtin_rules_only(&modulus_in_n_pos, verify_state)?;
        if !modulus_result.is_true() {
            return Ok(None);
        }

        let reason = if strict_upper_bound {
            "mod remainder upper bound: a % b < b for a in Z and b in N_pos"
        } else {
            "mod remainder nonnegative: 0 <= a % b for a in Z and b in N_pos"
        };
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                reason.to_string(),
                vec![dividend_result, modulus_result],
            ),
        )))
    }

    /// `n >= 1` / `1 <= n` from known `n $in Z` and `0 < n`.
    fn try_verify_order_one_le_from_membership_in_z_and_positive(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (n, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.right) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.left.clone(), f.line_file.clone())
            }
            AtomicFact::LessEqualFact(f) => {
                let Some(one) = self.resolve_obj_to_number(&f.left) else {
                    return Ok(None);
                };
                if !matches!(
                    compare_number_strings(&one.normalized_value, "1"),
                    NumberCompareResult::Equal
                ) {
                    return Ok(None);
                }
                (f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let in_z: AtomicFact =
            InFact::new(n.clone(), StandardSet::Z.into(), line_file.clone()).into();
        let positive: AtomicFact = LessFact::new(zero_obj, n, line_file.clone()).into();
        if !self
            .verify_non_equational_known_then_builtin_rules_only(&in_z, verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        if !self
            .verify_non_equational_known_then_builtin_rules_only(&positive, verify_state)?
            .is_true()
        {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "1 <= n from n $in Z and 0 < n".to_string(),
                Vec::new(),
            ),
        )))
    }

    /// Numeric lower-bound weakening, with the integer successor case.
    /// Examples: from `4 < x`, prove `2 <= x`; from `x $in Z` and `4 < x`, prove `5 <= x`.
    fn try_verify_numeric_lower_bound_from_known_lower_bound(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        match &norm {
            AtomicFact::LessEqualFact(f) => {
                let Some(target_bound) = self.resolved_integer_value_for_order_bound(&f.left)
                else {
                    return Ok(None);
                };
                let candidates = self.collect_known_lower_bound_candidates(&f.right);
                for candidate in candidates {
                    let Some((known_bound, known_strict)) =
                        self.known_lower_bound_candidate_value(&candidate, &f.right)
                    else {
                        continue;
                    };
                    let candidate_result =
                        self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
                    if !candidate_result.is_true() {
                        continue;
                    }
                    if target_bound <= known_bound {
                        return Ok(Some(StmtResult::from(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                atomic_fact.clone().into(),
                                "weaken numeric lower bound from known lower bound".to_string(),
                                vec![candidate_result],
                            ),
                        )));
                    }
                    if known_strict && known_bound.checked_add(1) == Some(target_bound) {
                        let in_z: AtomicFact = InFact::new(
                            f.right.clone(),
                            StandardSet::Z.into(),
                            f.line_file.clone(),
                        )
                        .into();
                        let in_z_result = self
                            .verify_non_equational_known_then_builtin_rules_only(
                                &in_z,
                                verify_state,
                            )?;
                        if !in_z_result.is_true() {
                            continue;
                        }
                        return Ok(Some(StmtResult::from(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                atomic_fact.clone().into(),
                                "integer weak lower bound from strict predecessor lower bound"
                                    .to_string(),
                                vec![candidate_result, in_z_result],
                            ),
                        )));
                    }
                }
            }
            AtomicFact::LessFact(f) => {
                let Some(target_bound) = self.resolved_integer_value_for_order_bound(&f.left)
                else {
                    return Ok(None);
                };
                let candidates = self.collect_known_lower_bound_candidates(&f.right);
                for candidate in candidates {
                    let Some((known_bound, known_strict)) =
                        self.known_lower_bound_candidate_value(&candidate, &f.right)
                    else {
                        continue;
                    };
                    let stronger_bound_is_enough = if known_strict {
                        target_bound <= known_bound
                    } else {
                        target_bound < known_bound
                    };
                    if !stronger_bound_is_enough {
                        continue;
                    }
                    let candidate_result =
                        self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
                    if candidate_result.is_true() {
                        return Ok(Some(StmtResult::from(
                            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                atomic_fact.clone().into(),
                                "weaken numeric strict lower bound from known lower bound"
                                    .to_string(),
                                vec![candidate_result],
                            ),
                        )));
                    }
                }
            }
            _ => {}
        }
        Ok(None)
    }

    fn collect_known_lower_bound_candidates(&self, right: &Obj) -> Vec<AtomicFact> {
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.known_atomic_facts_with_2_args.values() {
                for known_fact in known_facts_map.values() {
                    if self
                        .known_lower_bound_candidate_value(known_fact, right)
                        .is_some()
                    {
                        candidates.push(known_fact.clone());
                    }
                }
            }
        }
        candidates
    }

    fn known_lower_bound_candidate_value(
        &self,
        known_fact: &AtomicFact,
        right: &Obj,
    ) -> Option<(i128, bool)> {
        let norm = normalize_positive_order_atomic_fact(known_fact)?;
        match &norm {
            AtomicFact::LessFact(f) if f.right.to_string() == right.to_string() => {
                Some((self.resolved_integer_value_for_order_bound(&f.left)?, true))
            }
            AtomicFact::LessEqualFact(f) if f.right.to_string() == right.to_string() => {
                Some((self.resolved_integer_value_for_order_bound(&f.left)?, false))
            }
            _ => None,
        }
    }

    /// Numeric upper-bound weakening.
    /// Examples: from `x < 4`, prove `x <= 6`; from `x <= 4`, prove `x < 6`.
    fn try_verify_numeric_upper_bound_from_known_upper_bound(
        &mut self,
        atomic_fact: &AtomicFact,
        _verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let (target_bound, target_is_strict, target_left) = match &norm {
            AtomicFact::LessEqualFact(f) => (
                self.resolved_integer_value_for_order_bound(&f.right),
                false,
                &f.left,
            ),
            AtomicFact::LessFact(f) => (
                self.resolved_integer_value_for_order_bound(&f.right),
                true,
                &f.left,
            ),
            _ => return Ok(None),
        };
        let Some(target_bound) = target_bound else {
            return Ok(None);
        };

        for candidate in self.collect_known_upper_bound_candidates(target_left) {
            let Some((known_bound, known_is_strict)) =
                self.known_upper_bound_candidate_value(&candidate, target_left)
            else {
                continue;
            };
            let candidate_is_enough = if target_is_strict {
                known_bound < target_bound || (known_is_strict && known_bound == target_bound)
            } else {
                known_bound <= target_bound
            };
            if !candidate_is_enough {
                continue;
            }

            let candidate_result =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
            if !candidate_result.is_true() {
                continue;
            }
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "weaken numeric upper bound from known upper bound".to_string(),
                    vec![candidate_result],
                ),
            )));
        }
        Ok(None)
    }

    fn collect_known_upper_bound_candidates(&self, left: &Obj) -> Vec<AtomicFact> {
        let mut candidates = Vec::new();
        for environment in self.iter_environments_from_top() {
            for known_facts_map in environment.known_atomic_facts_with_2_args.values() {
                for known_fact in known_facts_map.values() {
                    if self
                        .known_upper_bound_candidate_value(known_fact, left)
                        .is_some()
                    {
                        candidates.push(known_fact.clone());
                    }
                }
            }
        }
        candidates
    }

    fn known_upper_bound_candidate_value(
        &self,
        known_fact: &AtomicFact,
        left: &Obj,
    ) -> Option<(i128, bool)> {
        let norm = normalize_positive_order_atomic_fact(known_fact)?;
        match &norm {
            AtomicFact::LessFact(f) if f.left.to_string() == left.to_string() => {
                Some((self.resolved_integer_value_for_order_bound(&f.right)?, true))
            }
            AtomicFact::LessEqualFact(f) if f.left.to_string() == left.to_string() => Some((
                self.resolved_integer_value_for_order_bound(&f.right)?,
                false,
            )),
            _ => None,
        }
    }

    fn resolved_integer_value_for_order_bound(&self, obj: &Obj) -> Option<i128> {
        let number = self.resolve_obj_to_number(obj)?;
        if !is_number_string_literally_integer_without_dot(number.normalized_value.clone()) {
            return None;
        }
        number.normalized_value.parse::<i128>().ok()
    }

    fn verify_zero_le_abs_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(f) = &norm else {
            return Ok(None);
        };
        if f.left.to_string() != "0" {
            return Ok(None);
        }
        if !matches!(&f.right, Obj::Abs(_)) {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= abs(x) for x in R".to_string(),
                Vec::new(),
            ),
        )))
    }

    // Principal square root is weakly nonnegative: `0 <= sqrt(x)` from `0 <= x`.
    // Example: `forall x R: x >= 0 =>: sqrt(x) >= 0`.
    fn verify_zero_le_sqrt_from_nonnegative_arg_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(f) = &norm else {
            return Ok(None);
        };
        if f.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Sqrt(sqrt) = &f.right else {
            return Ok(None);
        };
        let nonnegative_arg: AtomicFact = LessEqualFact::new(
            Number::new("0".to_string()).into(),
            sqrt.arg.as_ref().clone(),
            f.line_file.clone(),
        )
        .into();
        let nonnegative_result = self.verify_non_equational_known_then_builtin_rules_only(
            &nonnegative_arg,
            &VerifyState::new(0, true),
        )?;
        if !nonnegative_result.is_true() {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "sqrt: 0 <= sqrt(x) from 0 <= x".to_string(),
                vec![nonnegative_result],
            ),
        )))
    }

    // Principal square root preserves strict positivity: `0 < sqrt(x)` from `0 < x`.
    // Example: `forall x R: x > 0 =>: sqrt(x) > 0`.
    fn verify_zero_lt_sqrt_from_positive_arg_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessFact(f) = &norm else {
            return Ok(None);
        };
        if f.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Sqrt(sqrt) = &f.right else {
            return Ok(None);
        };
        let positive_arg: AtomicFact = LessFact::new(
            Number::new("0".to_string()).into(),
            sqrt.arg.as_ref().clone(),
            f.line_file.clone(),
        )
        .into();
        let positive_result = self.verify_non_equational_known_then_builtin_rules_only(
            &positive_arg,
            &VerifyState::new(0, true),
        )?;
        if !positive_result.is_true() {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "sqrt: 0 < sqrt(x) from 0 < x".to_string(),
                vec![positive_result],
            ),
        )))
    }

    // Principal square root is monotone on nonnegative reals.
    // Example: from `0 <= a`, `0 <= b`, and `a <= b`, prove `sqrt(a) <= sqrt(b)`.
    fn verify_sqrt_monotonicity_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        match &norm {
            AtomicFact::LessEqualFact(f) => self.try_verify_sqrt_monotonicity(
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
                false,
                atomic_fact,
            ),
            AtomicFact::LessFact(f) => self.try_verify_sqrt_monotonicity(
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
                true,
                atomic_fact,
            ),
            _ => Ok(None),
        }
    }

    fn try_verify_sqrt_monotonicity(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
        strict: bool,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (Obj::Sqrt(left_sqrt), Obj::Sqrt(right_sqrt)) = (&left, &right) else {
            return Ok(None);
        };
        let zero: Obj = Number::new("0".to_string()).into();
        let left_arg = left_sqrt.arg.as_ref().clone();
        let right_arg = right_sqrt.arg.as_ref().clone();
        let mut subgoals: Vec<AtomicFact> = vec![
            LessEqualFact::new(zero.clone(), left_arg.clone(), line_file.clone()).into(),
            LessEqualFact::new(zero, right_arg.clone(), line_file.clone()).into(),
        ];
        if strict {
            subgoals.push(LessFact::new(left_arg, right_arg, line_file).into());
        } else {
            subgoals.push(LessEqualFact::new(left_arg, right_arg, line_file).into());
        }

        let mut step_results = Vec::new();
        for subgoal in subgoals {
            let result = self.verify_non_equational_known_then_builtin_rules_only(
                &subgoal,
                &VerifyState::new(0, true),
            )?;
            if !result.is_true() {
                return Ok(None);
            }
            step_results.push(result);
        }

        let reason = if strict {
            "sqrt: sqrt(a) < sqrt(b) from 0 <= a, 0 <= b, and a < b"
        } else {
            "sqrt: sqrt(a) <= sqrt(b) from 0 <= a, 0 <= b, and a <= b"
        };
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                reason.to_string(),
                step_results,
            ),
        )))
    }

    // `(-1)*x` order vs 0: e.g. `x < 0` or `x <= 0` implies `(-1)*x >= 0`; `x > 0` implies `(-1)*x < 0`.
    // Also handles `0 <= (-1)*x` (equivalently `0 <= -x` when `-x` parses as `(-1)*x`).
    fn try_verify_order_opposite_sign_mul_minus_one(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let z: Obj = Number::new("0".to_string()).into();
        let success = |msg: &'static str| {
            Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    msg.to_string(),
                    Vec::new(),
                ),
            )))
        };
        match atomic_fact {
            AtomicFact::GreaterEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let le: AtomicFact =
                        LessEqualFact::new(x.clone(), z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&le, verify_state)?
                        .is_true()
                    {
                        return success("order: (-1)*x >= 0 from x <= 0");
                    }
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&lt, verify_state)?
                        .is_true()
                    {
                        return success("order: (-1)*x >= 0 from x < 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::GreaterFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&lt, verify_state)?
                        .is_true()
                    {
                        return success("order: (-1)*x > 0 from x < 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::LessEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let ge: AtomicFact =
                        GreaterEqualFact::new(x.clone(), z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&ge, verify_state)?
                        .is_true()
                    {
                        return success("order: (-1)*x <= 0 from x >= 0");
                    }
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&gt, verify_state)?
                        .is_true()
                    {
                        return success("order: (-1)*x <= 0 from x > 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::LessFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&gt, verify_state)?
                        .is_true()
                    {
                        return success("order: (-1)*x < 0 from x > 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::LessEqualFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let le: AtomicFact =
                        LessEqualFact::new(x.clone(), z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&le, verify_state)?
                        .is_true()
                    {
                        return success("order: 0 <= (-1)*x from x <= 0");
                    }
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&lt, verify_state)?
                        .is_true()
                    {
                        return success("order: 0 <= (-1)*x from x < 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::LessFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&lt, verify_state)?
                        .is_true()
                    {
                        return success("order: 0 < (-1)*x from x < 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::GreaterEqualFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let ge: AtomicFact =
                        GreaterEqualFact::new(x.clone(), z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&ge, verify_state)?
                        .is_true()
                    {
                        return success("order: 0 >= (-1)*x from x >= 0");
                    }
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&gt, verify_state)?
                        .is_true()
                    {
                        return success("order: 0 >= (-1)*x from x > 0");
                    }
                }
                Ok(None)
            }
            AtomicFact::GreaterFact(f) if self.obj_is_resolved_zero(&f.left) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.right) {
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_non_equational_known_then_builtin_rules_only(&gt, verify_state)?
                        .is_true()
                    {
                        return success("order: 0 > (-1)*x from x > 0");
                    }
                }
                Ok(None)
            }
            _ => Ok(None),
        }
    }

    // `a > b` from known `not (a <= b)`, `a < b` from `not (a >= b)`, etc. (total order duality).
    fn verify_order_from_known_negated_complement(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let negated: Option<AtomicFact> = match atomic_fact {
            AtomicFact::GreaterFact(f) => Some(
                NotLessEqualFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into(),
            ),
            AtomicFact::LessFact(f) => Some(
                NotGreaterEqualFact::new(f.left.clone(), f.right.clone(), f.line_file.clone())
                    .into(),
            ),
            AtomicFact::GreaterEqualFact(f) => {
                Some(NotLessFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into())
            }
            AtomicFact::LessEqualFact(f) => Some(
                NotGreaterFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into(),
            ),
            _ => None,
        };
        let Some(neg) = negated else {
            return Ok(None);
        };
        let sub = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&neg)?;
        if sub.is_true() {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                    atomic_fact.clone().into(),
                    InferResult::new(),
                    "order_from_known_negated_complement".to_string(),
                    vec![sub],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    // Logarithm order rules:
    // - base > 1 preserves order on positive arguments
    // - 0 < base < 1 reverses order on positive arguments
    // - with base > 1, log_a(x) is positive for x > 1 and negative for 0 < x < 1
    // Examples:
    // `forall a, x, y R_pos: a > 1, x < y =>: log(a, x) < log(a, y)`
    // `forall a, x R_pos: a > 1, x < 1 =>: log(a, x) < 0`
    fn verify_log_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let one = Self::literal_one_obj();
        let zero = Self::literal_zero_obj();
        let verify_state = VerifyState::new(0, true);

        if let AtomicFact::LessFact(f) = &norm {
            match (&f.left, &f.right) {
                (Obj::Log(left_log), Obj::Log(right_log)) => {
                    let same_base = self.verify_objs_are_equal_known_only(
                        left_log.base.as_ref(),
                        right_log.base.as_ref(),
                        f.line_file.clone(),
                    );
                    if !same_base.is_true() {
                        return Ok(None);
                    }

                    let base_gt_one: AtomicFact = LessFact::new(
                        one.clone(),
                        left_log.base.as_ref().clone(),
                        f.line_file.clone(),
                    )
                    .into();
                    let base_lt_one: AtomicFact = LessFact::new(
                        left_log.base.as_ref().clone(),
                        one.clone(),
                        f.line_file.clone(),
                    )
                    .into();
                    let forward_args: AtomicFact = LessFact::new(
                        left_log.arg.as_ref().clone(),
                        right_log.arg.as_ref().clone(),
                        f.line_file.clone(),
                    )
                    .into();
                    let reversed_args: AtomicFact = LessFact::new(
                        right_log.arg.as_ref().clone(),
                        left_log.arg.as_ref().clone(),
                        f.line_file.clone(),
                    )
                    .into();

                    let base_gt_one_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &base_gt_one,
                            &verify_state,
                        )?;
                    if base_gt_one_result.is_true() {
                        let args_result = self
                            .verify_non_equational_known_then_builtin_rules_only(
                                &forward_args,
                                &verify_state,
                            )?;
                        if args_result.is_true() {
                            return Ok(Some(StmtResult::from(
                                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                    atomic_fact.clone().into(),
                                    "log order: base > 1 preserves strict order".to_string(),
                                    vec![same_base, base_gt_one_result, args_result],
                                ),
                            )));
                        }
                    }

                    let base_lt_one_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &base_lt_one,
                            &verify_state,
                        )?;
                    if base_lt_one_result.is_true() {
                        let args_result = self
                            .verify_non_equational_known_then_builtin_rules_only(
                                &reversed_args,
                                &verify_state,
                            )?;
                        if args_result.is_true() {
                            return Ok(Some(StmtResult::from(
                                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                                    atomic_fact.clone().into(),
                                    "log order: 0 < base < 1 reverses strict order".to_string(),
                                    vec![same_base, base_lt_one_result, args_result],
                                ),
                            )));
                        }
                    }
                }
                (Obj::Number(left_number), Obj::Log(log))
                    if left_number.normalized_value == "0" =>
                {
                    let base_gt_one: AtomicFact =
                        LessFact::new(one.clone(), log.base.as_ref().clone(), f.line_file.clone())
                            .into();
                    let arg_gt_one: AtomicFact =
                        LessFact::new(one.clone(), log.arg.as_ref().clone(), f.line_file.clone())
                            .into();
                    let base_gt_one_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &base_gt_one,
                            &verify_state,
                        )?;
                    if !base_gt_one_result.is_true() {
                        return Ok(None);
                    }
                    let arg_gt_one_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &arg_gt_one,
                            &verify_state,
                        )?;
                    if !arg_gt_one_result.is_true() {
                        return Ok(None);
                    }
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "log sign: 0 < log(a, x) from 1 < a and 1 < x".to_string(),
                            vec![base_gt_one_result, arg_gt_one_result],
                        ),
                    )));
                }
                (Obj::Log(log), Obj::Number(right_number))
                    if right_number.normalized_value == "0" =>
                {
                    let base_gt_one: AtomicFact =
                        LessFact::new(one, log.base.as_ref().clone(), f.line_file.clone()).into();
                    let arg_lt_one: AtomicFact = LessFact::new(
                        log.arg.as_ref().clone(),
                        Self::literal_one_obj(),
                        f.line_file.clone(),
                    )
                    .into();
                    let arg_positive: AtomicFact =
                        LessFact::new(zero, log.arg.as_ref().clone(), f.line_file.clone()).into();
                    let base_gt_one_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &base_gt_one,
                            &verify_state,
                        )?;
                    if !base_gt_one_result.is_true() {
                        return Ok(None);
                    }
                    let arg_lt_one_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &arg_lt_one,
                            &verify_state,
                        )?;
                    if !arg_lt_one_result.is_true() {
                        return Ok(None);
                    }
                    let arg_positive_result = self
                        .verify_non_equational_known_then_builtin_rules_only(
                            &arg_positive,
                            &verify_state,
                        )?;
                    if !arg_positive_result.is_true() {
                        return Ok(None);
                    }
                    return Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "log sign: log(a, x) < 0 from 1 < a and 0 < x < 1".to_string(),
                            vec![base_gt_one_result, arg_lt_one_result, arg_positive_result],
                        ),
                    )));
                }
                _ => {}
            }
        }

        Ok(None)
    }

    // `not (a < b)` etc.: only consult known atomic facts for the equivalent weak/strict order.
    fn verify_negated_order_from_known_equivalent_order(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let candidates: Vec<AtomicFact> = match atomic_fact {
            AtomicFact::NotLessFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    LessEqualFact::new(f.right.clone(), f.left.clone(), lf.clone()).into(),
                    GreaterEqualFact::new(f.left.clone(), f.right.clone(), lf).into(),
                ]
            }
            AtomicFact::NotGreaterFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    LessEqualFact::new(f.left.clone(), f.right.clone(), lf.clone()).into(),
                    GreaterEqualFact::new(f.right.clone(), f.left.clone(), lf).into(),
                ]
            }
            AtomicFact::NotLessEqualFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    LessFact::new(f.right.clone(), f.left.clone(), lf.clone()).into(),
                    GreaterFact::new(f.left.clone(), f.right.clone(), lf).into(),
                ]
            }
            AtomicFact::NotGreaterEqualFact(f) => {
                let lf = f.line_file.clone();
                vec![
                    LessFact::new(f.left.clone(), f.right.clone(), lf.clone()).into(),
                    GreaterFact::new(f.right.clone(), f.left.clone(), lf).into(),
                ]
            }
            _ => return Ok(None),
        };
        for candidate in candidates {
            let sub = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&candidate)?;
            if sub.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        atomic_fact.clone().into(),
                        InferResult::new(),
                        "negated_order_from_known_equivalent_order".to_string(),
                        vec![sub],
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    // Matches Lit `a <= b` <=> `0 <= b - a` (and strict): `0 <= u - v` iff `v <= u`, `0 < u - v` iff `v < u`.
    fn verify_zero_order_on_sub_from_two_sided_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        match &norm {
            AtomicFact::LessEqualFact(f) if f.left.to_string() == "0" => {
                let Obj::Sub(sub) = &f.right else {
                    return Ok(None);
                };
                let derived: AtomicFact = LessEqualFact::new(
                    sub.right.as_ref().clone(),
                    sub.left.as_ref().clone(),
                    f.line_file.clone(),
                )
                .into();
                let mut result =
                    self.verify_non_equational_atomic_fact_with_known_atomic_facts(&derived)?;
                if !result.is_true() {
                    result = self.verify_order_atomic_fact_numeric_builtin_only(&derived)?;
                }
                if result.is_true() {
                    Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "0 <= u - v from v <= u".to_string(),
                            vec![result],
                        ),
                    )))
                } else {
                    Ok(None)
                }
            }
            AtomicFact::LessFact(f) if f.left.to_string() == "0" => {
                let Obj::Sub(sub) = &f.right else {
                    return Ok(None);
                };
                let derived: AtomicFact = LessFact::new(
                    sub.right.as_ref().clone(),
                    sub.left.as_ref().clone(),
                    f.line_file.clone(),
                )
                .into();
                let mut result =
                    self.verify_non_equational_atomic_fact_with_known_atomic_facts(&derived)?;
                if !result.is_true() {
                    result = self.verify_order_atomic_fact_numeric_builtin_only(&derived)?;
                }
                if result.is_true() {
                    Ok(Some(StmtResult::from(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            atomic_fact.clone().into(),
                            "0 < u - v from v < u".to_string(),
                            vec![result],
                        ),
                    )))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        }
    }

    fn verify_zero_le_add_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(less_equal_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_equal_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Add(add_obj) = &less_equal_fact.right else {
            return Ok(None);
        };

        let zero = &less_equal_fact.left;
        let line_file = &less_equal_fact.line_file;
        let left_verify_result =
            self.verify_zero_order_on_sub_expr(zero, add_obj.left.as_ref(), true, line_file)?;
        if !left_verify_result.is_true() {
            return Ok(None);
        }
        let right_verify_result =
            self.verify_zero_order_on_sub_expr(zero, add_obj.right.as_ref(), true, line_file)?;
        if !right_verify_result.is_true() {
            return Ok(None);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a + b from known atomic facts 0 <= a and 0 <= b".to_string(),
                vec![left_verify_result, right_verify_result],
            ),
        )))
    }

    fn verify_zero_lt_add_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessFact(less_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Add(add_obj) = &less_fact.right else {
            return Ok(None);
        };

        let zero = &less_fact.left;
        let line_file = &less_fact.line_file;

        let strict_then_weak = |this: &mut Self| -> Result<Option<StmtResult>, RuntimeError> {
            let left_result =
                this.verify_zero_order_on_sub_expr(zero, add_obj.left.as_ref(), false, line_file)?;
            if !left_result.is_true() {
                return Ok(None);
            }
            let right_result =
                this.verify_zero_order_on_sub_expr(zero, add_obj.right.as_ref(), true, line_file)?;
            if !right_result.is_true() {
                return Ok(None);
            }
            Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "0 < a + b from (0 < a and 0 <= b)".to_string(),
                    vec![left_result, right_result],
                ),
            )))
        };
        let weak_then_strict = |this: &mut Self| -> Result<Option<StmtResult>, RuntimeError> {
            let left_result =
                this.verify_zero_order_on_sub_expr(zero, add_obj.left.as_ref(), true, line_file)?;
            if !left_result.is_true() {
                return Ok(None);
            }
            let right_result =
                this.verify_zero_order_on_sub_expr(zero, add_obj.right.as_ref(), false, line_file)?;
            if !right_result.is_true() {
                return Ok(None);
            }
            Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "0 < a + b from (0 <= a and 0 < b)".to_string(),
                    vec![left_result, right_result],
                ),
            )))
        };

        if let Some(success) = strict_then_weak(self)? {
            return Ok(Some(success));
        }
        weak_then_strict(self)
    }

    fn verify_zero_le_even_integer_pow_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(less_equal_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_equal_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let right = &less_equal_fact.right;
        let is_equal_factors_mul = match right {
            Obj::Mul(mul_obj) => mul_obj.left.to_string() == mul_obj.right.to_string(),
            _ => false,
        };
        let is_even_pow = match right {
            Obj::Pow(pow_obj) => match pow_obj.exponent.as_ref() {
                Obj::Number(n) => normalized_decimal_string_is_even_integer(&n.normalized_value),
                _ => false,
            },
            _ => false,
        };
        if !is_equal_factors_mul && !is_even_pow {
            return Ok(None);
        }
        let msg = if is_equal_factors_mul {
            "0 <= a * a from even integer exponent (here 2) (forall a R)".to_string()
        } else {
            "0 <= a^n for even integer n (forall a R)".to_string()
        };
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                msg,
                Vec::new(),
            ),
        )))
    }

    fn verify_zero_lt_even_integer_pow_from_base_nonzero_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessFact(less_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Pow(pow_obj) = &less_fact.right else {
            return Ok(None);
        };
        let Obj::Number(exp_num) = pow_obj.exponent.as_ref() else {
            return Ok(None);
        };
        if !normalized_decimal_string_is_even_integer(&exp_num.normalized_value) {
            return Ok(None);
        }

        let line_file = less_fact.line_file.clone();
        let base = pow_obj.base.as_ref().clone();
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let base_neq_zero: AtomicFact = NotEqualFact::new(base, zero_obj, line_file.clone()).into();

        let neq_result = self.verify_non_equational_known_then_builtin_rules_only(
            &base_neq_zero,
            &VerifyState::new(0, true),
        )?;
        if !neq_result.is_true() {
            return Ok(None);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 < a^n for even integer n from a != 0".to_string(),
                vec![neq_result],
            ),
        )))
    }

    // Matches `0 < a^b` / `a^b > 0` when `0 < a` is proved (or known) and `b in R`.
    fn verify_zero_lt_pow_from_positive_base_real_exp_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessFact(less_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Pow(pow_obj) = &less_fact.right else {
            return Ok(None);
        };
        let zero = &less_fact.left;
        let line_file = &less_fact.line_file;
        let base = pow_obj.base.as_ref();
        let base_result = self.verify_zero_order_on_sub_expr(zero, base, false, line_file)?;
        if !base_result.is_true() {
            return Ok(None);
        }
        let in_r: AtomicFact = InFact::new(
            (*pow_obj.exponent).clone(),
            StandardSet::R.into(),
            line_file.clone(),
        )
        .into();
        let in_r_result = self.verify_non_equational_known_then_builtin_rules_only(
            &in_r,
            &VerifyState::new(0, true),
        )?;
        if !in_r_result.is_true() {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 < a^b from 0 < a and b in R".to_string(),
                vec![base_result, in_r_result],
            ),
        )))
    }

    // `0 <= a^b` / `a^b >= 0` with the same premises as strict `0 < a^b`: `0 < a` and `b in R`.
    // Covers symbolic exponents (e.g. `2^m`) where the literal-exponent `0 <= a^n` rule does not apply.
    fn verify_zero_le_pow_from_positive_base_real_exp_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(less_equal_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_equal_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Pow(pow_obj) = &less_equal_fact.right else {
            return Ok(None);
        };
        let zero = &less_equal_fact.left;
        let line_file = &less_equal_fact.line_file;
        let base = pow_obj.base.as_ref();
        let base_result = self.verify_zero_order_on_sub_expr(zero, base, false, line_file)?;
        if !base_result.is_true() {
            return Ok(None);
        }
        let in_r: AtomicFact = InFact::new(
            (*pow_obj.exponent).clone(),
            StandardSet::R.into(),
            line_file.clone(),
        )
        .into();
        let in_r_result = self.verify_non_equational_known_then_builtin_rules_only(
            &in_r,
            &VerifyState::new(0, true),
        )?;
        if !in_r_result.is_true() {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a^b from 0 < a and b in R".to_string(),
                vec![base_result, in_r_result],
            ),
        )))
    }

    // `0 <= a^n` / `a^n >= 0` when `0 <= a` and `n in N_pos`.
    // This covers symbolic positive integer exponents without needing `a > 0`.
    // Example: `forall a R, n N_pos: a >= 0 =>: a^n >= 0`.
    fn verify_zero_le_pow_from_nonnegative_base_positive_integer_exp_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(less_equal_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_equal_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Pow(pow_obj) = &less_equal_fact.right else {
            return Ok(None);
        };
        let zero = &less_equal_fact.left;
        let line_file = &less_equal_fact.line_file;
        let base = pow_obj.base.as_ref();
        let base_result = self.verify_zero_order_on_sub_expr(zero, base, true, line_file)?;
        if !base_result.is_true() {
            return Ok(None);
        }
        let in_n_pos: AtomicFact = InFact::new(
            (*pow_obj.exponent).clone(),
            StandardSet::NPos.into(),
            line_file.clone(),
        )
        .into();
        let in_n_pos_result = self.verify_non_equational_known_then_builtin_rules_only(
            &in_n_pos,
            &VerifyState::new(0, true),
        )?;
        if !in_n_pos_result.is_true() {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a^n from 0 <= a and n in N_pos".to_string(),
                vec![base_result, in_n_pos_result],
            ),
        )))
    }

    fn verify_zero_le_pow_integer_exponent_from_nonneg_base_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(less_equal_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_equal_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Pow(pow_obj) = &less_equal_fact.right else {
            return Ok(None);
        };
        let Obj::Number(exp_num) = pow_obj.exponent.as_ref() else {
            return Ok(None);
        };
        if !normalized_decimal_string_is_integer(&exp_num.normalized_value) {
            return Ok(None);
        }

        let zero = &less_equal_fact.left;
        let line_file = &less_equal_fact.line_file;
        let base = pow_obj.base.as_ref();

        let exponent_vs_zero = compare_normalized_number_str_to_zero(&exp_num.normalized_value);
        let base_result = match exponent_vs_zero {
            NumberCompareResult::Less => {
                self.verify_zero_order_on_sub_expr(zero, base, false, line_file)?
            }
            NumberCompareResult::Equal | NumberCompareResult::Greater => {
                self.verify_zero_order_on_sub_expr(zero, base, true, line_file)?
            }
        };
        if !base_result.is_true() {
            return Ok(None);
        }

        let msg = match exponent_vs_zero {
            NumberCompareResult::Less => "0 <= a^n from 0 < a and integer n < 0".to_string(),
            _ => "0 <= a^n from 0 <= a and integer n".to_string(),
        };

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                msg,
                vec![base_result],
            ),
        )))
    }

    fn verify_zero_le_mul_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(less_equal_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_equal_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Mul(mul_obj) = &less_equal_fact.right else {
            return Ok(None);
        };

        let zero = &less_equal_fact.left;
        let line_file = &less_equal_fact.line_file;
        let left_verify_result =
            self.verify_zero_order_on_sub_expr(zero, mul_obj.left.as_ref(), true, line_file)?;
        if !left_verify_result.is_true() {
            return Ok(None);
        }
        let right_verify_result =
            self.verify_zero_order_on_sub_expr(zero, mul_obj.right.as_ref(), true, line_file)?;
        if !right_verify_result.is_true() {
            return Ok(None);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a * b from 0 <= a and 0 <= b".to_string(),
                vec![left_verify_result, right_verify_result],
            ),
        )))
    }

    fn verify_zero_lt_mul_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessFact(less_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Mul(mul_obj) = &less_fact.right else {
            return Ok(None);
        };

        let zero = &less_fact.left;
        let line_file = &less_fact.line_file;
        let left_verify_result =
            self.verify_zero_order_on_sub_expr(zero, mul_obj.left.as_ref(), false, line_file)?;
        if !left_verify_result.is_true() {
            return Ok(None);
        }
        let right_verify_result =
            self.verify_zero_order_on_sub_expr(zero, mul_obj.right.as_ref(), false, line_file)?;
        if !right_verify_result.is_true() {
            return Ok(None);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 < a * b from 0 < a and 0 < b".to_string(),
                vec![left_verify_result, right_verify_result],
            ),
        )))
    }

    fn verify_zero_le_div_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessEqualFact(less_equal_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_equal_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Div(div_obj) = &less_equal_fact.right else {
            return Ok(None);
        };

        let zero = &less_equal_fact.left;
        let line_file = &less_equal_fact.line_file;
        let numer_result =
            self.verify_zero_order_on_sub_expr(zero, div_obj.left.as_ref(), true, line_file)?;
        if !numer_result.is_true() {
            return Ok(None);
        }
        let denom_result =
            self.verify_zero_order_on_sub_expr(zero, div_obj.right.as_ref(), false, line_file)?;
        if !denom_result.is_true() {
            return Ok(None);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a / b from 0 <= a and 0 < b".to_string(),
                vec![numer_result, denom_result],
            ),
        )))
    }

    fn verify_zero_lt_div_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let AtomicFact::LessFact(less_fact) = normalized_fact else {
            return Ok(None);
        };
        if less_fact.left.to_string() != "0" {
            return Ok(None);
        }
        let Obj::Div(div_obj) = &less_fact.right else {
            return Ok(None);
        };

        let zero = &less_fact.left;
        let line_file = &less_fact.line_file;
        let numer_result =
            self.verify_zero_order_on_sub_expr(zero, div_obj.left.as_ref(), false, line_file)?;
        if !numer_result.is_true() {
            return Ok(None);
        }
        let denom_result =
            self.verify_zero_order_on_sub_expr(zero, div_obj.right.as_ref(), false, line_file)?;
        if !denom_result.is_true() {
            return Ok(None);
        }

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 < a / b from 0 < a and 0 < b".to_string(),
                vec![numer_result, denom_result],
            ),
        )))
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
