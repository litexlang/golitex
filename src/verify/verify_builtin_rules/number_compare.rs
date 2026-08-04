use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;
use crate::verify::verify_equality_by_builtin_rules::verify_equality_by_they_are_the_same;

impl Runtime {
    // The nonnegative / positive cone under field operations is checked here on normalized
    // `0 <=` / `0 <` goals (possibly after `normalize_positive_order_atomic_fact`):
    // - Chained `+`: `0 <= a + b + …` from `0 <=` on each peeled summand; `0 < a + b + …` from
    //   `(0 < a ∧ 0 <= b) ∨ (0 <= a ∧ 0 < b)` at each binary `+`.
    // - Powers: literal even integer exponent ⇒ `0 <= base^n`; literal integer exponent and `0 <= base`
    //   (or `0 < base` if exponent < 0) ⇒ `0 <= base^n`; `a * a` with equal factors; `0 < base^exp`
    //   from `0 < base` and `exp in R`.
    // - Products and quotients: `0 <= a * b`, `0 < a * b`, `0 <= a / b` (denominator strictly
    //   positive), `0 < a / b`, each with recursive sub-goals on operands.
    // Difference/order bridges and strict-square facts are checked below as target rules, without
    // loading trusted Lit declarations. This path bridges `0 <= u - v` / `0 < u - v` and
    // `v <= u` / `v < u` in both directions.
    // Algebraic closure (+, -, *, /) on general `a <= b` / `a < b` is in `order_algebra_builtin.rs`.
    pub fn verify_order_atomic_fact_numeric_builtin_only(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        // Most rules in this dispatcher are facts about the real-number order.
        // The direct order-semantics rules above additionally handle integer
        // discreteness and numeric transitivity after their own type checks.
        // Example: `a R, b R, a < b` may yield `a <= b`; set-valued operands may not.
        let (left, right, line_file) = match atomic_fact {
            AtomicFact::LessFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::GreaterFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::LessEqualFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::GreaterEqualFact(f) => {
                (f.left.clone(), f.right.clone(), f.line_file.clone())
            }
            AtomicFact::NotLessFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::NotGreaterFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::NotLessEqualFact(f) => {
                (f.left.clone(), f.right.clone(), f.line_file.clone())
            }
            AtomicFact::NotGreaterEqualFact(f) => {
                (f.left.clone(), f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(StmtUnknown::new().into()),
        };
        // Every positive common divisor is bounded by the gcd.
        // Example: `d in N+`, `a % d = 0`, `b % d = 0` imply `d <= gcd(a, b)`.
        if let (AtomicFact::LessEqualFact(_), Obj::Gcd(gcd)) = (atomic_fact, &right) {
            let d_in_n_pos: AtomicFact =
                InFact::new(left.clone(), StandardSet::NPos.into(), line_file.clone()).into();
            let left_divisible: AtomicFact = EqualFact::new(
                Mod::new((*gcd.left).clone(), left.clone()).into(),
                Number::new("0".to_string()).into(),
                line_file.clone(),
            )
            .into();
            let right_divisible: AtomicFact = EqualFact::new(
                Mod::new((*gcd.right).clone(), left.clone()).into(),
                Number::new("0".to_string()).into(),
                line_file.clone(),
            )
            .into();
            let mut subgoals = Vec::new();
            for premise in [d_in_n_pos, left_divisible, right_divisible] {
                let result = self.verify_builtin_rule_premise(&premise, builtin_state)?;
                if result.is_unknown() {
                    subgoals.clear();
                    break;
                }
                subgoals.push(result);
            }
            if subgoals.len() == 3 {
                return Ok(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "every positive common divisor is at most the gcd".to_string(),
                        subgoals,
                    )
                    .into(),
                );
            }
        }
        if self
            .verify_objects_are_known_reals_in_builtin(&[&left, &right], &line_file, builtin_state)?
            .is_none()
        {
            return Ok(StmtUnknown::new().into());
        }
        // Dispatch exact cone shapes before the generic order semantics.
        if let Some(result) = self
            .verify_zero_le_add_from_known_atomic_facts_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self
            .verify_zero_lt_add_from_known_atomic_facts_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_le_even_integer_pow_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.verify_zero_lt_even_integer_pow_from_base_nonzero_builtin_rule(
            atomic_fact,
            builtin_state,
        )? {
            return Ok(result);
        }
        if let Some(result) = self.verify_zero_lt_pow_from_positive_base_real_exp_builtin_rule(
            atomic_fact,
            builtin_state,
        )? {
            return Ok(result);
        }
        if let Some(result) = self
            .verify_zero_le_pow_from_nonnegative_base_positive_integer_exp_builtin_rule(
                atomic_fact,
                builtin_state,
            )?
        {
            return Ok(result);
        }
        if let Some(result) = self
            .verify_zero_le_pow_integer_exponent_from_nonneg_base_builtin_rule(
                atomic_fact,
                builtin_state,
            )?
        {
            return Ok(result);
        }
        if let Some(result) = self.verify_zero_le_pow_from_positive_base_real_exp_builtin_rule(
            atomic_fact,
            builtin_state,
        )? {
            return Ok(result);
        }
        if let Some(result) = self
            .verify_zero_le_mul_from_known_atomic_facts_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self
            .verify_zero_lt_mul_from_known_atomic_facts_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self
            .verify_zero_le_div_from_known_atomic_facts_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self
            .verify_zero_lt_div_from_known_atomic_facts_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.verify_abs_order_builtin_rule(atomic_fact, builtin_state)? {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_abs_order_strict_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_rounding_extrema_order(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_exp_sign_factorial_order(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = try_verify_native_real_constant_positive(atomic_fact) {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_trigonometric_order_bound(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_order_semantics_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_native_complex_abs_order(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_finite_nonempty_set_size_at_least_one(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_finite_set_size_nonnegative(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_finite_set_size_subset_le(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self
            .try_verify_finite_set_size_codomain_le_domain_from_known_surjection(
                atomic_fact,
                builtin_state,
            )?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_finite_set_size_union_or_set_diff_le_sum(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_order_nonnegative_from_membership_in_n(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_order_one_le_from_membership_in_n_pos(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self
            .try_verify_order_one_le_from_membership_in_n_and_nonzero(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self
            .try_verify_order_one_le_from_membership_in_z_and_positive(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_numeric_lower_bound_from_known_lower_bound(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_numeric_upper_bound_from_known_upper_bound(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.try_verify_mod_remainder_bounds(atomic_fact, builtin_state)? {
            return Ok(result);
        }
        if let Some(result) =
            self.try_verify_order_opposite_sign_mul_minus_one(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_order_from_known_negated_complement(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_negated_order_from_known_equivalent_order(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.verify_zero_le_abs_builtin_rule(atomic_fact)? {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_le_sqrt_from_nonnegative_arg_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_zero_lt_sqrt_from_positive_arg_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_sqrt_monotonicity_builtin_rule(atomic_fact, builtin_state)?
        {
            return Ok(result);
        }
        if let Some(result) = self.verify_log_order_builtin_rule(atomic_fact, builtin_state)? {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_order_from_known_zero_order_on_sub_builtin_rule(atomic_fact)?
        {
            return Ok(result);
        }
        if let Some(result) = self.verify_zero_order_on_sub_from_two_sided_order_builtin_rule(
            atomic_fact,
            builtin_state,
        )? {
            return Ok(result);
        }
        if let Some(result) =
            self.verify_order_algebra_structural_builtin_rule(atomic_fact, builtin_state)?
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
            let equal_result = self.verify_objs_are_equal_by_known_equality(
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
            let equal_result = self.verify_objs_are_equal_by_known_equality(
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
        Ok(StmtResult::Unknown(StmtUnknown::new()))
    }

    pub(in crate::verify) fn verify_number_comparison_builtin_rule(
        &self,
        atomic_fact: &AtomicFact,
    ) -> Option<bool> {
        let normalized = normalize_positive_order_atomic_fact(atomic_fact)?;
        match normalized {
            AtomicFact::LessFact(less_fact) => {
                if verify_equality_by_they_are_the_same(&less_fact.left, &less_fact.right) {
                    return Some(false);
                }
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
                if verify_equality_by_they_are_the_same(
                    &less_equal_fact.left,
                    &less_equal_fact.right,
                ) {
                    return Some(true);
                }
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

// Euler's number and pi are primitive positive real constants. The canonical
// rational bounds expose `e > 1` and `3 < pi < 4` without decimal approximation.
// Example: `0 < e`, `e > 1`, `3 < pi`, and `pi < 4`.
fn try_verify_native_real_constant_positive(atomic_fact: &AtomicFact) -> Option<StmtResult> {
    let is_zero = |obj: &Obj| {
        matches!(
            obj,
            Obj::Number(number) if number.normalized_value == "0"
        )
    };
    let is_native_positive_constant = |obj: &Obj| matches!(obj, Obj::EulerNumber(_) | Obj::Pi(_));
    let is_one = |obj: &Obj| {
        matches!(
            obj,
            Obj::Number(number) if number.normalized_value == "1"
        )
    };
    let is_e = |obj: &Obj| matches!(obj, Obj::EulerNumber(_));
    let is_pi = |obj: &Obj| matches!(obj, Obj::Pi(_));
    let is_number = |obj: &Obj, expected: &str| matches!(obj, Obj::Number(number) if number.normalized_value == expected);
    let applies = match atomic_fact {
        AtomicFact::LessFact(fact) => {
            (is_zero(&fact.left) && is_native_positive_constant(&fact.right))
                || (is_one(&fact.left) && is_e(&fact.right))
                || (is_number(&fact.left, "3") && is_pi(&fact.right))
                || (is_pi(&fact.left) && is_number(&fact.right, "4"))
        }
        AtomicFact::GreaterFact(fact) => {
            (is_native_positive_constant(&fact.left) && is_zero(&fact.right))
                || (is_e(&fact.left) && is_one(&fact.right))
                || (is_pi(&fact.left) && is_number(&fact.right, "3"))
                || (is_number(&fact.left, "4") && is_pi(&fact.right))
        }
        _ => false,
    };
    if !applies {
        return None;
    }
    Some(
        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
            atomic_fact.clone().into(),
            "native mathematical constant positivity bound".to_string(),
            Vec::new(),
        )
        .into(),
    )
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
    fn verify_zero_order_on_sub_expr(
        &mut self,
        zero: &Obj,
        sub_expr: &Obj,
        weak: bool,
        parent_weak: bool,
        line_file: &LineFile,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let fact: AtomicFact = if weak {
            LessEqualFact::new(zero.clone(), sub_expr.clone(), line_file.clone()).into()
        } else {
            LessFact::new(zero.clone(), sub_expr.clone(), line_file.clone()).into()
        };
        if weak == parent_weak {
            self.verify_builtin_rule_premise(&fact, builtin_state)
        } else {
            self.verify_builtin_rule_premise(&fact, builtin_state)
        }
    }

    /// `n >= 0` / `0 <= n` from known `n $in N` (e.g. `forall n N:` domain).
    fn try_verify_order_nonnegative_from_membership_in_n(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let in_n_result = self.verify_builtin_rule_premise(&in_n, builtin_state)?;
        if in_n_result.is_true() {
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "n >= 0 from n $in N".to_string(),
                    vec![in_n_result],
                ),
            )));
        }
        Ok(None)
    }

    /// `n >= 1` / `1 <= n` from known `n $in N+`.
    fn try_verify_order_one_le_from_membership_in_n_pos(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let in_n_pos_result = self.verify_builtin_rule_premise(&in_n_pos, builtin_state)?;
        if in_n_pos_result.is_true() {
            return Ok(Some(StmtResult::from(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    "n >= 1 from n $in N+".to_string(),
                    vec![in_n_pos_result],
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let finite_result = self.verify_builtin_rule_premise(&finite, builtin_state)?;
        if !finite_result.is_true() {
            return Ok(None);
        }

        let nonempty: AtomicFact = IsNonemptySetFact::new(set, line_file).into();
        let nonempty_result = self.verify_builtin_rule_premise(&nonempty, builtin_state)?;
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

    // Cardinality is nonnegative even when the finite set may be empty.
    // Keep this direct bridge separate from the nonempty lower bound so a
    // symbolic `finite_set` parameter does not need a recursive N-membership
    // round merely to prove `finite_set_size(S) >= 0`.
    fn try_verify_finite_set_size_nonnegative(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let is_zero =
            |obj: &Obj| matches!(obj, Obj::Number(number) if number.normalized_value == "0");
        let (size, line_file) = match atomic_fact {
            AtomicFact::GreaterEqualFact(f) if is_zero(&f.right) => (&f.left, f.line_file.clone()),
            AtomicFact::LessEqualFact(f) if is_zero(&f.left) => (&f.right, f.line_file.clone()),
            _ => return Ok(None),
        };
        let Obj::FiniteSetSize(size) = size else {
            return Ok(None);
        };
        let finite: AtomicFact = IsFiniteSetFact::new(size.set.as_ref().clone(), line_file).into();
        let result = self.verify_builtin_rule_premise(&finite, builtin_state)?;
        if !result.is_true() {
            return Ok(None);
        }
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "finite set cardinality is nonnegative".to_string(),
                vec![result],
            )
            .into(),
        ))
    }

    // The cardinality of a finite subset is at most that of its finite container.
    // Example: `A $subset B` with finite `A` and `B` gives
    // `finite_set_size(A) <= finite_set_size(B)`.
    fn try_verify_finite_set_size_subset_le(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (left_size, right_size, line_file) = match atomic_fact {
            AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right, fact.line_file.clone()),
            AtomicFact::GreaterEqualFact(fact) => (&fact.right, &fact.left, fact.line_file.clone()),
            _ => return Ok(None),
        };
        let Obj::FiniteSetSize(left_size) = left_size else {
            return Ok(None);
        };
        let Obj::FiniteSetSize(right_size) = right_size else {
            return Ok(None);
        };

        if let Obj::Intersect(intersection) = left_size.set.as_ref() {
            let right_matches_left = verify_equality_by_they_are_the_same(
                intersection.left.as_ref(),
                right_size.set.as_ref(),
            );
            let right_matches_right = verify_equality_by_they_are_the_same(
                intersection.right.as_ref(),
                right_size.set.as_ref(),
            );
            if right_matches_left || right_matches_right {
                let left_input: AtomicFact =
                    IsFiniteSetFact::new(intersection.left.as_ref().clone(), line_file.clone())
                        .into();
                let right_input: AtomicFact =
                    IsFiniteSetFact::new(intersection.right.as_ref().clone(), line_file.clone())
                        .into();
                let left_result = self.verify_builtin_rule_premise(&left_input, builtin_state)?;
                let right_result = self.verify_builtin_rule_premise(&right_input, builtin_state)?;
                if left_result.is_true() && right_result.is_true() {
                    return Ok(Some(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                            atomic_fact.clone().into(),
                            InferResult::new(),
                            "finite_set_size_subset_le".to_string(),
                            vec![left_result, right_result],
                        )
                        .into(),
                    ));
                }
            }
        }

        let subset: AtomicFact = SubsetFact::new(
            left_size.set.as_ref().clone(),
            right_size.set.as_ref().clone(),
            line_file.clone(),
        )
        .into();
        let mut subset_result = self.verify_builtin_rule_premise(&subset, builtin_state)?;
        if !subset_result.is_true() {
            let superset: AtomicFact = SupersetFact::new(
                right_size.set.as_ref().clone(),
                left_size.set.as_ref().clone(),
                line_file.clone(),
            )
            .into();
            subset_result = self.verify_known_non_forall_atomic_fact(&superset)?;
        }
        if !subset_result.is_true() {
            return Ok(None);
        }

        let left_finite: AtomicFact =
            IsFiniteSetFact::new(left_size.set.as_ref().clone(), line_file.clone()).into();
        let left_result = self.verify_builtin_rule_premise(&left_finite, builtin_state)?;
        if !left_result.is_true() {
            return Ok(None);
        }

        let right_finite: AtomicFact =
            IsFiniteSetFact::new(right_size.set.as_ref().clone(), line_file).into();
        let right_result = self.verify_builtin_rule_premise(&right_finite, builtin_state)?;
        if !right_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                atomic_fact.clone().into(),
                InferResult::new(),
                "finite_set_size_subset_le".to_string(),
                vec![subset_result, left_result, right_result],
            )
            .into(),
        ))
    }

    // A union or symmetric difference has at most the sum of its two finite inputs.
    // Examples: `finite_set_size(union(A, B)) <= finite_set_size(A) + finite_set_size(B)`
    // and `finite_set_size(set_diff(A, B)) <= finite_set_size(A) + finite_set_size(B)`.
    fn try_verify_finite_set_size_union_or_set_diff_le_sum(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (smaller, larger, line_file) = match atomic_fact {
            AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right, fact.line_file.clone()),
            AtomicFact::GreaterEqualFact(fact) => (&fact.right, &fact.left, fact.line_file.clone()),
            _ => return Ok(None),
        };
        let Obj::FiniteSetSize(combined_size) = smaller else {
            return Ok(None);
        };
        let Obj::Add(sum) = larger else {
            return Ok(None);
        };
        let Obj::FiniteSetSize(left_size) = sum.left.as_ref() else {
            return Ok(None);
        };
        let Obj::FiniteSetSize(right_size) = sum.right.as_ref() else {
            return Ok(None);
        };

        let (left_set, right_set, rule) = match combined_size.set.as_ref() {
            Obj::Union(union) => (
                union.left.as_ref().clone(),
                union.right.as_ref().clone(),
                "finite_set_size_union_le_sum",
            ),
            Obj::SetDiff(set_diff) => (
                set_diff.left.as_ref().clone(),
                set_diff.right.as_ref().clone(),
                "finite_set_size_set_diff_le_sum",
            ),
            _ => return Ok(None),
        };
        if !verify_equality_by_they_are_the_same(&left_set, &left_size.set)
            || !verify_equality_by_they_are_the_same(&right_set, &right_size.set)
        {
            return Ok(None);
        }

        let left_finite: AtomicFact = IsFiniteSetFact::new(left_set, line_file.clone()).into();
        let left_result = self.verify_builtin_rule_premise(&left_finite, builtin_state)?;
        if !left_result.is_true() {
            return Ok(None);
        }
        let right_finite: AtomicFact = IsFiniteSetFact::new(right_set, line_file).into();
        let right_result = self.verify_builtin_rule_premise(&right_finite, builtin_state)?;
        if !right_result.is_true() {
            return Ok(None);
        }

        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                atomic_fact.clone().into(),
                InferResult::new(),
                rule.to_string(),
                vec![left_result, right_result],
            )
            .into(),
        ))
    }

    /// `n >= 1` / `1 <= n` from known `n $in N` and `n != 0` (nonzero naturals are at least 1).
    /// Example: `forall x N: x != 0 =>: 1 <= x`.
    fn try_verify_order_one_le_from_membership_in_n_and_nonzero(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let nonzero: AtomicFact = NotEqualFact::new(n.clone(), zero_obj, line_file.clone()).into();
        let mut in_n_result = self.verify_builtin_rule_premise(&in_n, builtin_state)?;
        if !in_n_result.is_true() {
            if let Obj::FiniteSetSize(finite_set_size) = &n {
                let in_n_fact = InFact::new(n.clone(), StandardSet::N.into(), line_file.clone());
                in_n_result = self.verify_finite_set_size_in_standard_number_set(
                    &in_n_fact,
                    finite_set_size,
                    builtin_state,
                )?;
            }
        }
        if !in_n_result.is_true() {
            return Ok(None);
        }
        let nonzero_result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(&nonzero)?;
        if !nonzero_result.is_true() {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "1 <= n from n $in N and n != 0".to_string(),
                vec![in_n_result, nonzero_result],
            ),
        )))
    }

    /// Euclidean remainders modulo a positive integer lie in the standard interval.
    /// Example: from `a $in Z` and `b $in N+`, prove `0 <= a % b < b`.
    fn try_verify_mod_remainder_bounds(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let dividend_result = self.verify_builtin_rule_premise(&dividend_in_z, builtin_state)?;
        if !dividend_result.is_true() {
            return Ok(None);
        }

        let modulus_in_n_pos: AtomicFact = InFact::new(
            mod_obj.right.as_ref().clone(),
            StandardSet::NPos.into(),
            line_file,
        )
        .into();
        let modulus_result = self.verify_builtin_rule_premise(&modulus_in_n_pos, builtin_state)?;
        if !modulus_result.is_true() {
            return Ok(None);
        }

        let reason = if strict_upper_bound {
            "mod remainder upper bound: a % b < b for a in Z and b in N+"
        } else {
            "mod remainder nonnegative: 0 <= a % b for a in Z and b in N+"
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let in_z_result = self.verify_builtin_rule_premise(&in_z, builtin_state)?;
        if !in_z_result.is_true() {
            return Ok(None);
        }
        let positive_result = self.verify_builtin_rule_premise(&positive, builtin_state)?;
        if !positive_result.is_true() {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "1 <= n from n $in Z and 0 < n".to_string(),
                vec![in_z_result, positive_result],
            ),
        )))
    }

    /// Numeric lower-bound weakening, with the integer successor case.
    /// Examples: from `4 < x`, prove `2 <= x`; from `x $in Z` and `4 < x`, prove `5 <= x`.
    fn try_verify_numeric_lower_bound_from_known_lower_bound(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
                        let in_z_result = self.verify_builtin_rule_premise(&in_z, builtin_state)?;
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
        _builtin_state: &UseBuiltinRuleVerifyState,
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let nonnegative_result =
            self.verify_builtin_rule_premise(&nonnegative_arg, builtin_state)?;
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let positive_result = self.verify_builtin_rule_premise(&positive_arg, builtin_state)?;
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
                builtin_state,
            ),
            AtomicFact::LessFact(f) => self.try_verify_sqrt_monotonicity(
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
                true,
                atomic_fact,
                builtin_state,
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
            let result = self.verify_builtin_rule_premise(&subgoal, builtin_state)?;
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

    // Negation reverses order; it also specializes to sign facts at zero.
    // Example: `x < -5` implies `-x > 5`.
    fn try_verify_order_opposite_sign_mul_minus_one(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
            AtomicFact::GreaterFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact =
                        LessFact::new(x, negative_right, f.line_file.clone()).into();
                    if self
                        .verify_builtin_rule_premise(&reverse, builtin_state)?
                        .is_true()
                    {
                        return success("order: -x > y from x < -y");
                    }
                }
            }
            AtomicFact::GreaterEqualFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact =
                        LessEqualFact::new(x, negative_right, f.line_file.clone()).into();
                    if self
                        .verify_builtin_rule_premise(&reverse, builtin_state)?
                        .is_true()
                    {
                        return success("order: -x >= y from x <= -y");
                    }
                }
            }
            AtomicFact::LessFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact =
                        GreaterFact::new(x, negative_right, f.line_file.clone()).into();
                    if self
                        .verify_builtin_rule_premise(&reverse, builtin_state)?
                        .is_true()
                    {
                        return success("order: -x < y from x > -y");
                    }
                }
            }
            AtomicFact::LessEqualFact(f) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let negative_right: Obj =
                        Mul::new(Number::new("-1".to_string()).into(), f.right.clone()).into();
                    let reverse: AtomicFact =
                        GreaterEqualFact::new(x, negative_right, f.line_file.clone()).into();
                    if self
                        .verify_builtin_rule_premise(&reverse, builtin_state)?
                        .is_true()
                    {
                        return success("order: -x <= y from x >= -y");
                    }
                }
            }
            _ => {}
        }
        match atomic_fact {
            AtomicFact::GreaterEqualFact(f) if self.obj_is_resolved_zero(&f.right) => {
                if let Some(x) = self.peel_mul_by_literal_neg_one(&f.left) {
                    let le: AtomicFact =
                        LessEqualFact::new(x.clone(), z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_builtin_rule_premise(&le, builtin_state)?
                        .is_true()
                    {
                        return success("order: (-1)*x >= 0 from x <= 0");
                    }
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_builtin_rule_premise(&lt, builtin_state)?
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
                        .verify_builtin_rule_premise(&lt, builtin_state)?
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
                        .verify_builtin_rule_premise(&ge, builtin_state)?
                        .is_true()
                    {
                        return success("order: (-1)*x <= 0 from x >= 0");
                    }
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_builtin_rule_premise(&gt, builtin_state)?
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
                        .verify_builtin_rule_premise(&gt, builtin_state)?
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
                        .verify_builtin_rule_premise(&le, builtin_state)?
                        .is_true()
                    {
                        return success("order: 0 <= (-1)*x from x <= 0");
                    }
                    let lt: AtomicFact = LessFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_builtin_rule_premise(&lt, builtin_state)?
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
                        .verify_builtin_rule_premise(&lt, builtin_state)?
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
                        .verify_builtin_rule_premise(&ge, builtin_state)?
                        .is_true()
                    {
                        return success("order: 0 >= (-1)*x from x >= 0");
                    }
                    let gt: AtomicFact = GreaterFact::new(x, z.clone(), f.line_file.clone()).into();
                    if self
                        .verify_builtin_rule_premise(&gt, builtin_state)?
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
                        .verify_builtin_rule_premise(&gt, builtin_state)?
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
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (neg, left, right, line_file) = match atomic_fact {
            AtomicFact::GreaterFact(f) => (
                NotLessEqualFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            AtomicFact::LessFact(f) => (
                NotGreaterEqualFact::new(f.left.clone(), f.right.clone(), f.line_file.clone())
                    .into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            AtomicFact::GreaterEqualFact(f) => (
                NotLessFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            AtomicFact::LessEqualFact(f) => (
                NotGreaterFact::new(f.left.clone(), f.right.clone(), f.line_file.clone()).into(),
                f.left.clone(),
                f.right.clone(),
                f.line_file.clone(),
            ),
            _ => return Ok(None),
        };
        let Some(mut steps) = self.verify_objects_are_known_reals_in_builtin(
            &[&left, &right],
            &line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let sub = self.verify_non_equational_atomic_fact_with_known_atomic_facts(&neg)?;
        if sub.is_true() {
            steps.push(sub);
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                    atomic_fact.clone().into(),
                    InferResult::new(),
                    "order_from_known_negated_complement".to_string(),
                    steps,
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
    // `forall a, x, y R+: a > 1, x < y =>: log(a, x) < log(a, y)`
    // `forall a, x R+: a > 1, x < 1 =>: log(a, x) < 0`
    fn verify_log_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let one = Self::literal_one_obj();
        let zero = Self::literal_zero_obj();

        if let AtomicFact::LessFact(f) = &norm {
            match (&f.left, &f.right) {
                (Obj::Log(left_log), Obj::Log(right_log)) => {
                    let same_base = self.verify_objs_are_equal_by_known_equality(
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

                    let base_gt_one_result =
                        self.verify_builtin_rule_premise(&base_gt_one, builtin_state)?;
                    if base_gt_one_result.is_true() {
                        let args_result =
                            self.verify_builtin_rule_premise(&forward_args, builtin_state)?;
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

                    let base_lt_one_result =
                        self.verify_builtin_rule_premise(&base_lt_one, builtin_state)?;
                    if base_lt_one_result.is_true() {
                        let args_result =
                            self.verify_builtin_rule_premise(&reversed_args, builtin_state)?;
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
                    let base_gt_one_result =
                        self.verify_builtin_rule_premise(&base_gt_one, builtin_state)?;
                    if !base_gt_one_result.is_true() {
                        return Ok(None);
                    }
                    let arg_gt_one_result =
                        self.verify_builtin_rule_premise(&arg_gt_one, builtin_state)?;
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
                    let base_gt_one_result =
                        self.verify_builtin_rule_premise(&base_gt_one, builtin_state)?;
                    if !base_gt_one_result.is_true() {
                        return Ok(None);
                    }
                    let arg_lt_one_result =
                        self.verify_builtin_rule_premise(&arg_lt_one, builtin_state)?;
                    if !arg_lt_one_result.is_true() {
                        return Ok(None);
                    }
                    let arg_positive_result =
                        self.verify_builtin_rule_premise(&arg_positive, builtin_state)?;
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
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let (left, right, line_file) = match atomic_fact {
            AtomicFact::NotLessFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::NotGreaterFact(f) => (f.left.clone(), f.right.clone(), f.line_file.clone()),
            AtomicFact::NotLessEqualFact(f) => {
                (f.left.clone(), f.right.clone(), f.line_file.clone())
            }
            AtomicFact::NotGreaterEqualFact(f) => {
                (f.left.clone(), f.right.clone(), f.line_file.clone())
            }
            _ => return Ok(None),
        };
        let Some(mut steps) = self.verify_objects_are_known_reals_in_builtin(
            &[&left, &right],
            &line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
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
                steps.push(sub);
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_label_and_steps(
                        atomic_fact.clone().into(),
                        InferResult::new(),
                        "negated_order_from_known_equivalent_order".to_string(),
                        steps,
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    // Moves a known difference bound back to the corresponding order fact.
    // Examples: from `a - b <= 0` or `0 <= b - a`, prove `a <= b`.
    fn verify_order_from_known_zero_order_on_sub_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(atomic_fact) else {
            return Ok(None);
        };
        let (left, right, is_weak, line_file) = match normalized_fact {
            AtomicFact::LessEqualFact(f) => (f.left, f.right, true, f.line_file),
            AtomicFact::LessFact(f) => (f.left, f.right, false, f.line_file),
            _ => return Ok(None),
        };

        let zero = Self::literal_zero_obj();
        let direct_difference: Obj = Sub::new(left.clone(), right.clone()).into();
        let direct_difference_order: AtomicFact = if is_weak {
            LessEqualFact::new(direct_difference, zero.clone(), line_file.clone()).into()
        } else {
            LessFact::new(direct_difference, zero.clone(), line_file.clone()).into()
        };
        let direct_difference_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_facts(&direct_difference_order)?;
        if direct_difference_result.is_true() {
            let reason = if is_weak {
                "a <= b from a - b <= 0"
            } else {
                "a < b from a - b < 0"
            };
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    atomic_fact.clone().into(),
                    reason.to_string(),
                    vec![direct_difference_result],
                )
                .into(),
            ));
        }

        let difference: Obj = Sub::new(right, left).into();
        let difference_order: AtomicFact = if is_weak {
            LessEqualFact::new(zero, difference, line_file).into()
        } else {
            LessFact::new(zero, difference, line_file).into()
        };
        let difference_result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(&difference_order)?;
        if !difference_result.is_true() {
            return Ok(None);
        }

        let reason = if is_weak {
            "a <= b from 0 <= b - a"
        } else {
            "a < b from 0 < b - a"
        };
        Ok(Some(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                reason.to_string(),
                vec![difference_result],
            )
            .into(),
        ))
    }

    // Matches Lit `a <= b` <=> `0 <= b - a` (and strict): `0 <= u - v` iff `v <= u`, `0 < u - v` iff `v < u`.
    fn verify_zero_order_on_sub_from_two_sided_order_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
                let result = self.verify_builtin_rule_premise(&derived, builtin_state)?;
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
                let result = self.verify_builtin_rule_premise(&derived, builtin_state)?;
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let left_verify_result = self.verify_zero_order_on_sub_expr(
            zero,
            add_obj.left.as_ref(),
            true,
            true,
            line_file,
            builtin_state,
        )?;
        if !left_verify_result.is_true() {
            return Ok(None);
        }
        let right_verify_result = self.verify_zero_order_on_sub_expr(
            zero,
            add_obj.right.as_ref(),
            true,
            true,
            line_file,
            builtin_state,
        )?;
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
        builtin_state: &UseBuiltinRuleVerifyState,
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

        let left_strict = self.verify_zero_order_on_sub_expr(
            zero,
            add_obj.left.as_ref(),
            false,
            false,
            line_file,
            builtin_state,
        )?;
        if left_strict.is_true() {
            let right_strict = self.verify_zero_order_on_sub_expr(
                zero,
                add_obj.right.as_ref(),
                false,
                false,
                line_file,
                builtin_state,
            )?;
            if right_strict.is_true() {
                return Ok(Some(StmtResult::from(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        atomic_fact.clone().into(),
                        "0 < a + b from 0 < a and 0 < b".to_string(),
                        vec![left_strict, right_strict],
                    ),
                )));
            }
        }

        let strict_then_weak = |this: &mut Self,
                                builtin_state: &UseBuiltinRuleVerifyState|
         -> Result<Option<StmtResult>, RuntimeError> {
            let left_result = this.verify_zero_order_on_sub_expr(
                zero,
                add_obj.left.as_ref(),
                false,
                false,
                line_file,
                builtin_state,
            )?;
            if !left_result.is_true() {
                return Ok(None);
            }
            let right_result = this.verify_zero_order_on_sub_expr(
                zero,
                add_obj.right.as_ref(),
                true,
                false,
                line_file,
                builtin_state,
            )?;
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
        let weak_then_strict = |this: &mut Self,
                                builtin_state: &UseBuiltinRuleVerifyState|
         -> Result<Option<StmtResult>, RuntimeError> {
            let left_result = this.verify_zero_order_on_sub_expr(
                zero,
                add_obj.left.as_ref(),
                true,
                false,
                line_file,
                builtin_state,
            )?;
            if !left_result.is_true() {
                return Ok(None);
            }
            let right_result = this.verify_zero_order_on_sub_expr(
                zero,
                add_obj.right.as_ref(),
                false,
                false,
                line_file,
                builtin_state,
            )?;
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

        if let Some(success) = strict_then_weak(self, builtin_state)? {
            return Ok(Some(success));
        }
        weak_then_strict(self, builtin_state)
    }

    pub(super) fn verify_zero_le_even_integer_pow_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let (base, is_equal_factors_mul, is_even_pow) = match right {
            Obj::Mul(mul_obj) if mul_obj.left.to_string() == mul_obj.right.to_string() => {
                (mul_obj.left.as_ref(), true, false)
            }
            Obj::Pow(pow_obj) => {
                let Obj::Number(n) = pow_obj.exponent.as_ref() else {
                    return Ok(None);
                };
                if !normalized_decimal_string_is_even_integer(&n.normalized_value) {
                    return Ok(None);
                }
                (pow_obj.base.as_ref(), false, true)
            }
            _ => return Ok(None),
        };
        if !is_equal_factors_mul && !is_even_pow {
            return Ok(None);
        }
        let Some(steps) = self.verify_objects_are_known_reals_in_builtin(
            &[base],
            &less_equal_fact.line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let msg = if is_equal_factors_mul {
            "0 <= a * a from even integer exponent (here 2) (forall a R)".to_string()
        } else {
            "0 <= a^n for even integer n (forall a R)".to_string()
        };
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                msg,
                steps,
            ),
        )))
    }

    // An even power or repeated factor is strictly positive when its base is nonzero.
    // Example: from `a != 0`, prove `0 < a^2` or `0 < a * a`.
    fn verify_zero_lt_even_integer_pow_from_base_nonzero_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let line_file = less_fact.line_file.clone();
        let (base, reason) = match &less_fact.right {
            Obj::Pow(pow_obj) => {
                let Obj::Number(exp_num) = pow_obj.exponent.as_ref() else {
                    return Ok(None);
                };
                if !normalized_decimal_string_is_even_integer(&exp_num.normalized_value) {
                    return Ok(None);
                }
                (
                    pow_obj.base.as_ref().clone(),
                    "0 < a^n for even integer n from a != 0",
                )
            }
            Obj::Mul(mul_obj) if mul_obj.left.to_string() == mul_obj.right.to_string() => {
                (mul_obj.left.as_ref().clone(), "0 < a * a from a != 0")
            }
            _ => return Ok(None),
        };
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let Some(mut steps) =
            self.verify_objects_are_known_reals_in_builtin(&[&base], &line_file, builtin_state)?
        else {
            return Ok(None);
        };
        let base_neq_zero: AtomicFact = NotEqualFact::new(base, zero_obj, line_file.clone()).into();

        let neq_result = self.verify_builtin_rule_premise(&base_neq_zero, builtin_state)?;
        if !neq_result.is_true() {
            return Ok(None);
        }
        steps.push(neq_result);

        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                reason.to_string(),
                steps,
            ),
        )))
    }

    // Matches `0 < a^b` / `a^b > 0` when `0 < a` is proved (or known) and `b in R`.
    fn verify_zero_lt_pow_from_positive_base_real_exp_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let base_result =
            self.verify_zero_order_on_sub_expr(zero, base, false, false, line_file, builtin_state)?;
        if !base_result.is_true() {
            return Ok(None);
        }
        let Some(mut exponent_steps) = self.verify_objects_are_known_reals_in_builtin(
            &[pow_obj.exponent.as_ref()],
            line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let mut steps = vec![base_result];
        steps.append(&mut exponent_steps);
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 < a^b from 0 < a and b in R".to_string(),
                steps,
            ),
        )))
    }

    // `0 <= a^b` / `a^b >= 0` with the same premises as strict `0 < a^b`: `0 < a` and `b in R`.
    // Covers symbolic exponents (e.g. `2^m`) where the literal-exponent `0 <= a^n` rule does not apply.
    fn verify_zero_le_pow_from_positive_base_real_exp_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let base_result =
            self.verify_zero_order_on_sub_expr(zero, base, false, true, line_file, builtin_state)?;
        if !base_result.is_true() {
            return Ok(None);
        }
        let Some(mut exponent_steps) = self.verify_objects_are_known_reals_in_builtin(
            &[pow_obj.exponent.as_ref()],
            line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let mut steps = vec![base_result];
        steps.append(&mut exponent_steps);
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a^b from 0 < a and b in R".to_string(),
                steps,
            ),
        )))
    }

    // `0 <= a^n` / `a^n >= 0` when `0 <= a` and `n in N+`.
    // This covers symbolic positive integer exponents without needing `a > 0`.
    // Example: `forall a R, n N+: a >= 0 =>: a^n >= 0`.
    fn verify_zero_le_pow_from_nonnegative_base_positive_integer_exp_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let base_result =
            self.verify_zero_order_on_sub_expr(zero, base, true, true, line_file, builtin_state)?;
        if !base_result.is_true() {
            return Ok(None);
        }
        let in_n_pos: AtomicFact = InFact::new(
            (*pow_obj.exponent).clone(),
            StandardSet::NPos.into(),
            line_file.clone(),
        )
        .into();
        let in_n_pos_result = self.verify_builtin_rule_premise(&in_n_pos, builtin_state)?;
        if !in_n_pos_result.is_true() {
            return Ok(None);
        }
        Ok(Some(StmtResult::from(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a^n from 0 <= a and n in N+".to_string(),
                vec![base_result, in_n_pos_result],
            ),
        )))
    }

    fn verify_zero_le_pow_integer_exponent_from_nonneg_base_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
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
            NumberCompareResult::Less => self.verify_zero_order_on_sub_expr(
                zero,
                base,
                false,
                true,
                line_file,
                builtin_state,
            )?,
            NumberCompareResult::Equal | NumberCompareResult::Greater => self
                .verify_zero_order_on_sub_expr(zero, base, true, true, line_file, builtin_state)?,
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let left_verify_result = self.verify_zero_order_on_sub_expr(
            zero,
            mul_obj.left.as_ref(),
            true,
            true,
            line_file,
            builtin_state,
        )?;
        if !left_verify_result.is_true() {
            return Ok(None);
        }
        let right_verify_result = self.verify_zero_order_on_sub_expr(
            zero,
            mul_obj.right.as_ref(),
            true,
            true,
            line_file,
            builtin_state,
        )?;
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let left_verify_result = self.verify_zero_order_on_sub_expr(
            zero,
            mul_obj.left.as_ref(),
            false,
            false,
            line_file,
            builtin_state,
        )?;
        if !left_verify_result.is_true() {
            return Ok(None);
        }
        let right_verify_result = self.verify_zero_order_on_sub_expr(
            zero,
            mul_obj.right.as_ref(),
            false,
            false,
            line_file,
            builtin_state,
        )?;
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let numer_result = self.verify_zero_order_on_sub_expr(
            zero,
            div_obj.left.as_ref(),
            true,
            true,
            line_file,
            builtin_state,
        )?;
        if !numer_result.is_true() {
            return Ok(None);
        }
        let denom_result = self.verify_zero_order_on_sub_expr(
            zero,
            div_obj.right.as_ref(),
            false,
            true,
            line_file,
            builtin_state,
        )?;
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
        builtin_state: &UseBuiltinRuleVerifyState,
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
        let numer_result = self.verify_zero_order_on_sub_expr(
            zero,
            div_obj.left.as_ref(),
            false,
            false,
            line_file,
            builtin_state,
        )?;
        if !numer_result.is_true() {
            return Ok(None);
        }
        let denom_result = self.verify_zero_order_on_sub_expr(
            zero,
            div_obj.right.as_ref(),
            false,
            false,
            line_file,
            builtin_state,
        )?;
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
