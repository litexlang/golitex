//! Power nonnegativity and positivity.

use super::*;

impl Runtime {
    pub(in crate::verification) fn verify_zero_le_even_integer_pow_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                msg,
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyZeroLeEvenIntegerPowBuiltinRule,
                ),
                steps,
            ),
        )))
    }

    // An even power or repeated factor is strictly positive when its base is nonzero.
    // Example: from `a != 0`, prove `0 < a^2` or `0 < a * a`.
    pub(in crate::verification) fn verify_zero_lt_even_integer_pow_from_base_nonzero_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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

        let Some(neq_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&base_neq_zero, builtin_state)?
        else {
            return Ok(None);
        };
        steps.push(neq_result);

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                reason.to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyZeroLtEvenIntegerPowFromBaseNonzeroBuiltinRule,
                ),
                steps,
            ),
        )))
    }

    // Matches `0 < a^b` / `a^b > 0` when `0 < a` is proved (or known) and `b in R`.
    pub(in crate::verification) fn verify_zero_lt_pow_from_positive_base_real_exp_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
        let Some(base_result) =
            self.verify_zero_order_on_sub_expr(zero, base, false, line_file, builtin_state)?
        else {
            return Ok(None);
        };
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
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "0 < a^b from 0 < a and b in R".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyZeroLtPowFromPositiveBaseRealExpBuiltinRule,
                ),
                steps,
            ),
        )))
    }

    // `0 <= a^b` / `a^b >= 0` with the same premises as strict `0 < a^b`: `0 < a` and `b in R`.
    // Covers symbolic exponents (e.g. `2^m`) where the literal-exponent `0 <= a^n` rule does not apply.
    pub(in crate::verification) fn verify_zero_le_pow_from_positive_base_real_exp_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
        let Some(base_result) =
            self.verify_zero_order_on_sub_expr(zero, base, false, line_file, builtin_state)?
        else {
            return Ok(None);
        };
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
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a^b from 0 < a and b in R".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyZeroLePowFromPositiveBaseRealExpBuiltinRule,
                ),
                steps,
            ),
        )))
    }

    // `0 <= a^n` / `a^n >= 0` when `0 <= a` and `n in N+`.
    // This covers symbolic positive integer exponents without needing `a > 0`.
    // Example: `forall a R, n N+: a >= 0 =>: a^n >= 0`.
    pub(in crate::verification) fn verify_zero_le_pow_from_nonnegative_base_positive_integer_exp_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
        let Some(base_result) =
            self.verify_zero_order_on_sub_expr(zero, base, true, line_file, builtin_state)?
        else {
            return Ok(None);
        };
        let in_n_pos: AtomicFact = InFact::new(
            (*pow_obj.exponent).clone(),
            StandardSet::NPos.into(),
            line_file.clone(),
        )
        .into();
        let Some(in_n_pos_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&in_n_pos, builtin_state)?
        else {
            return Ok(None);
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a^n from 0 <= a and n in N+".to_string(),
                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyZeroLePowFromNonnegativeBasePositiveIntegerExpBuiltinRule),
                vec![base_result, in_n_pos_result],
            ),
        )))
    }

    pub(in crate::verification) fn verify_zero_le_pow_integer_exponent_from_nonneg_base_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
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
                self.verify_zero_order_on_sub_expr(zero, base, false, line_file, builtin_state)?
            }
            NumberCompareResult::Equal | NumberCompareResult::Greater => {
                self.verify_zero_order_on_sub_expr(zero, base, true, line_file, builtin_state)?
            }
        };
        let Some(base_result) = base_result else {
            return Ok(None);
        };

        let msg = match exponent_vs_zero {
            NumberCompareResult::Less => "0 <= a^n from 0 < a and integer n < 0".to_string(),
            _ => "0 <= a^n from 0 <= a and integer n".to_string(),
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                msg,
                BuiltinRuleEvidence::Uncatalogued(UncataloguedBuiltinRule::VerifyZeroLePowIntegerExponentFromNonnegBaseBuiltinRule),
                vec![base_result],
            ),
        )))
    }
}
