//! Nonnegative and positive addition.

use super::*;

impl Runtime {
    pub(in crate::verification) fn verify_zero_le_add_from_known_atomic_facts_builtin_rule(
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
        if !left_verify_result.is_success() {
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
        if !right_verify_result.is_success() {
            return Ok(None);
        }

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a + b from known atomic facts 0 <= a and 0 <= b".to_string(),
                BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::AddNonnegative),
                vec![left_verify_result, right_verify_result],
            ),
        )))
    }

    pub(in crate::verification) fn verify_zero_lt_add_from_known_atomic_facts_builtin_rule(
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
        if left_strict.is_success() {
            let right_strict = self.verify_zero_order_on_sub_expr(
                zero,
                add_obj.right.as_ref(),
                false,
                false,
                line_file,
                builtin_state,
            )?;
            if right_strict.is_success() {
                return Ok(Some(ProveFactResult::from(
                    SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                        atomic_fact.clone().into(),
                        "0 < a + b from 0 < a and 0 < b".to_string(),
                        BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::AddPositive),
                        vec![left_strict, right_strict],
                    ),
                )));
            }
        }

        let strict_then_weak = |this: &mut Self,
                                builtin_state: &BuiltinRuleSearchState|
         -> Result<Option<ProveFactResult>, RuntimeError> {
            let left_result = this.verify_zero_order_on_sub_expr(
                zero,
                add_obj.left.as_ref(),
                false,
                false,
                line_file,
                builtin_state,
            )?;
            if !left_result.is_success() {
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
            if !right_result.is_success() {
                return Ok(None);
            }
            Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "0 < a + b from (0 < a and 0 <= b)".to_string(),
                    BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::AddPositiveLeftStrict),
                    vec![left_result, right_result],
                ),
            )))
        };
        let weak_then_strict = |this: &mut Self,
                                builtin_state: &BuiltinRuleSearchState|
         -> Result<Option<ProveFactResult>, RuntimeError> {
            let left_result = this.verify_zero_order_on_sub_expr(
                zero,
                add_obj.left.as_ref(),
                true,
                false,
                line_file,
                builtin_state,
            )?;
            if !left_result.is_success() {
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
            if !right_result.is_success() {
                return Ok(None);
            }
            Ok(Some(ProveFactResult::from(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    atomic_fact.clone().into(),
                    "0 < a + b from (0 <= a and 0 < b)".to_string(),
                    BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::AddPositiveRightStrict),
                    vec![left_result, right_result],
                ),
            )))
        };

        if let Some(success) = strict_then_weak(self, builtin_state)? {
            return Ok(Some(success));
        }
        weak_then_strict(self, builtin_state)
    }
}
