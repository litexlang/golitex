//! Numeric order dispatch and native real constant positivity.

use super::*;

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
    // loading trusted Lit definitions. This path bridges `0 <= u - v` / `0 < u - v` and
    // `v <= u` / `v < u` in both directions.
    // Algebraic closure (+, -, *, /) on general `a <= b` / `a < b` is in `order_algebra_builtin.rs`.
    pub fn verify_order_atomic_fact_numeric_builtin_only(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<ProveFactResult, RuntimeError> {
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
            _ => return Ok(UnknownGenericStmtResult::new().into()),
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
            if let Some(subgoals) = self.verify_builtin_rule_premises(
                &[d_in_n_pos, left_divisible, right_divisible],
                builtin_state,
            )? {
                return Ok(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "every positive common divisor is at most the gcd".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyOrderAtomicFactNumericBuiltinOnly01),
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
            return Ok(UnknownGenericStmtResult::new().into());
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
            self.try_verify_finite_set_size_union_le_sum(atomic_fact, builtin_state)?
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
            self.verify_order_from_known_zero_order_on_sub_builtin_rule(atomic_fact, builtin_state)?
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
                return Ok(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        less_equal_fact.clone().into(),
                        "less_equal_fact_equal".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyOrderAtomicFactNumericBuiltinOnly02),
                        Vec::new(),
                    ),
                ));
            }
            let equal_result = self.try_verify_known_equality_fact_candidate(
                &EqualFact::new_from_refs(
                    &less_equal_fact.left,
                    &less_equal_fact.right,
                    less_equal_fact.line_file.clone(),
                ),
                builtin_state.verify_state(),
            )?;
            if let Some(equal_result) = equal_result {
                return Ok(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        less_equal_fact.clone().into(),
                        "less_equal_fact_from_known_equality".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyOrderAtomicFactNumericBuiltinOnly03),
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
                self.try_verify_atomic_fact_as_builtin_rule_premise(&strict_atomic, builtin_state)?;
            if let Some(strict_result) = strict_result {
                return Ok(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        less_equal_fact.clone().into(),
                        "less_equal_fact_from_known_strict_order".to_string(),
                        BuiltinRuleEvidence::Arithmetic(
                            ArithmeticBuiltinRule::LessEqualFromStrictOrder,
                        ),
                        vec![strict_result],
                    ),
                ));
            }
        }
        if let AtomicFact::GreaterEqualFact(greater_equal_fact) = atomic_fact {
            if greater_equal_fact.left.to_string() == greater_equal_fact.right.to_string() {
                return Ok(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        greater_equal_fact.clone().into(),
                        "greater_equal_fact_equal".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyOrderAtomicFactNumericBuiltinOnly04),
                        Vec::new(),
                    ),
                ));
            }
            let equal_result = self.try_verify_known_equality_fact_candidate(
                &EqualFact::new_from_refs(
                    &greater_equal_fact.left,
                    &greater_equal_fact.right,
                    greater_equal_fact.line_file.clone(),
                ),
                builtin_state.verify_state(),
            )?;
            if let Some(equal_result) = equal_result {
                return Ok(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        greater_equal_fact.clone().into(),
                        "greater_equal_fact_from_known_equality".to_string(),
                        BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyOrderAtomicFactNumericBuiltinOnly05),
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
                self.try_verify_atomic_fact_as_builtin_rule_premise(&strict_atomic, builtin_state)?;
            if let Some(strict_result) = strict_result {
                return Ok(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        greater_equal_fact.clone().into(),
                        "greater_equal_fact_from_known_strict_order".to_string(),
                        BuiltinRuleEvidence::Arithmetic(
                            ArithmeticBuiltinRule::GreaterEqualFromStrictOrder,
                        ),
                        vec![strict_result],
                    ),
                ));
            }
        }
        Ok(UnknownGenericStmtResult::new().into())
    }

    pub(in crate::verification) fn verify_number_comparison_builtin_rule(
        &self,
        atomic_fact: &AtomicFact,
    ) -> Option<BuiltinRuleEvidence> {
        let normalized = normalize_positive_order_atomic_fact(atomic_fact)?;
        let (left, right, allow_equal) = match &normalized {
            AtomicFact::LessFact(fact) => (&fact.left, &fact.right, false),
            AtomicFact::LessEqualFact(fact) => (&fact.left, &fact.right, true),
            _ => return None,
        };

        if objs_match_for_pattern(left, right) {
            return allow_equal.then(|| {
                BuiltinRuleEvidence::OrderReflexivity(OrderReflexivityBuiltinRuleEvidence::new(
                    atomic_fact.clone().into(),
                    left.clone(),
                ))
            });
        }

        if let (Some(left_evaluation), Some(right_evaluation)) = (
            left.evaluate_to_normalized_decimal_number_with_result(),
            right.evaluate_to_normalized_decimal_number_with_result(),
        ) {
            let comparison = compare_number_strings(
                &left_evaluation.value.normalized_value,
                &right_evaluation.value.normalized_value,
            );
            let succeeds = matches!(comparison, NumberCompareResult::Less)
                || (allow_equal && matches!(comparison, NumberCompareResult::Equal));
            return succeeds.then(|| {
                BuiltinRuleEvidence::ClosedNumericComparison(
                    ClosedNumericComparisonBuiltinRuleEvidence::new(
                        atomic_fact.clone().into(),
                        left_evaluation,
                        right_evaluation,
                    ),
                )
            });
        }

        if let Some((left_value, right_value)) =
            self.calculate_obj_pair_to_number_strings(left, right)
        {
            let comparison = compare_number_strings(&left_value, &right_value);
            let succeeds = matches!(comparison, NumberCompareResult::Less)
                || (allow_equal && matches!(comparison, NumberCompareResult::Equal));
            return succeeds.then(|| {
                BuiltinRuleEvidence::RuntimeResolvedNumericComparison(
                    RuntimeResolvedNumericComparisonBuiltinRuleEvidence::new(
                        atomic_fact.clone().into(),
                        Number::new(left_value).into(),
                        Number::new(right_value).into(),
                    ),
                )
            });
        }

        self.try_verify_numeric_order_via_div_elimination(left, right, allow_equal)
            .and_then(|succeeds| {
                succeeds.then(|| {
                    BuiltinRuleEvidence::RuntimeResolvedNumericComparison(
                        RuntimeResolvedNumericComparisonBuiltinRuleEvidence::new(
                            atomic_fact.clone().into(),
                            self.resolve_obj(left),
                            self.resolve_obj(right),
                        ),
                    )
                })
            })
    }
}

// Euler's number and pi are primitive positive real constants. The canonical
// rational bounds expose `e > 1` and `3 < pi < 4` without decimal approximation.
// Example: `0 < e`, `e > 1`, `3 < pi`, and `pi < 4`.
fn try_verify_native_real_constant_positive(atomic_fact: &AtomicFact) -> Option<ProveFactResult> {
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
        SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
            atomic_fact.clone().into(),
            "native mathematical constant positivity bound".to_string(),
            BuiltinRuleEvidence::Uncatalogued(
                UncataloguedBuiltinRule::TryVerifyNativeRealConstantPositive,
            ),
            Vec::new(),
        )
        .into(),
    )
}
