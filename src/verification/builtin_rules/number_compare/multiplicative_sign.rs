//! Product and quotient sign rules.

use super::*;

impl Runtime {
    pub(in crate::verification) fn verify_zero_le_mul_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
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
            line_file,
            builtin_state,
        )?;
        let Some(left_verify_result) = left_verify_result else {
            return Ok(None);
        };
        let right_verify_result = self.verify_zero_order_on_sub_expr(
            zero,
            mul_obj.right.as_ref(),
            true,
            line_file,
            builtin_state,
        )?;
        let Some(right_verify_result) = right_verify_result else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a * b from 0 <= a and 0 <= b".to_string(),
                BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::MulNonnegative),
                vec![left_verify_result, right_verify_result],
            ),
        )))
    }

    pub(in crate::verification) fn verify_zero_lt_mul_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
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
            line_file,
            builtin_state,
        )?;
        let Some(left_verify_result) = left_verify_result else {
            return Ok(None);
        };
        let right_verify_result = self.verify_zero_order_on_sub_expr(
            zero,
            mul_obj.right.as_ref(),
            false,
            line_file,
            builtin_state,
        )?;
        let Some(right_verify_result) = right_verify_result else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "0 < a * b from 0 < a and 0 < b".to_string(),
                BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::MulPositive),
                vec![left_verify_result, right_verify_result],
            ),
        )))
    }

    pub(in crate::verification) fn verify_zero_le_div_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
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
            line_file,
            builtin_state,
        )?;
        let Some(numer_result) = numer_result else {
            return Ok(None);
        };
        let denom_result = self.verify_zero_order_on_sub_expr(
            zero,
            div_obj.right.as_ref(),
            false,
            line_file,
            builtin_state,
        )?;
        let Some(denom_result) = denom_result else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= a / b from 0 <= a and 0 < b".to_string(),
                BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::DivNonnegative),
                vec![numer_result, denom_result],
            ),
        )))
    }

    pub(in crate::verification) fn verify_zero_lt_div_from_known_atomic_facts_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(normalized_fact) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
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
            line_file,
            builtin_state,
        )?;
        let Some(numer_result) = numer_result else {
            return Ok(None);
        };
        let denom_result = self.verify_zero_order_on_sub_expr(
            zero,
            div_obj.right.as_ref(),
            false,
            line_file,
            builtin_state,
        )?;
        let Some(denom_result) = denom_result else {
            return Ok(None);
        };

        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "0 < a / b from 0 < a and 0 < b".to_string(),
                BuiltinRuleEvidence::Arithmetic(ArithmeticBuiltinRule::DivPositive),
                vec![numer_result, denom_result],
            ),
        )))
    }

    pub(in crate::verification) fn calculate_obj_pair_to_number_strings(
        &self,
        left_obj: &Obj,
        right_obj: &Obj,
    ) -> Option<(String, String)> {
        let left_number = self.resolve_obj_to_number_resolved(left_obj)?;
        let right_number = self.resolve_obj_to_number_resolved(right_obj)?;
        Some((left_number.normalized_value, right_number.normalized_value))
    }
}
