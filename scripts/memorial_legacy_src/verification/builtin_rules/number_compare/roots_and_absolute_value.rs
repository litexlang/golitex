//! Absolute-value and square-root order rules.

use super::*;

impl Runtime {
    pub(in crate::verification) fn verify_zero_le_abs_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
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
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "0 <= abs(x) for x in R".to_string(),
                BuiltinRuleEvidence::AbsoluteValue(AbsoluteValueBuiltinRule::Nonnegative),
                Vec::new(),
            ),
        )))
    }

    // Principal square root is weakly nonnegative: `0 <= sqrt(x)` from `0 <= x`.
    // Example: `forall x R: x >= 0 =>: sqrt(x) >= 0`.
    pub(in crate::verification) fn verify_zero_le_sqrt_from_nonnegative_arg_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
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
        let nonnegative_arg: AtomicFact = self
            .new_less_equal_fact(
                Number::new("0".to_string()).into(),
                sqrt.arg.as_ref().clone(),
                f.line_file.clone(),
            )
            .into();
        let Some(nonnegative_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&nonnegative_arg, builtin_state)?
        else {
            return Ok(None);
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "sqrt: 0 <= sqrt(x) from 0 <= x".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyZeroLeSqrtFromNonnegativeArgBuiltinRule,
                ),
                vec![nonnegative_result],
            ),
        )))
    }

    // Principal square root preserves strict positivity: `0 < sqrt(x)` from `0 < x`.
    // Example: `forall x R: x > 0 =>: sqrt(x) > 0`.
    pub(in crate::verification) fn verify_zero_lt_sqrt_from_positive_arg_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
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
        let positive_arg: AtomicFact = self
            .new_less_fact(
                Number::new("0".to_string()).into(),
                sqrt.arg.as_ref().clone(),
                f.line_file.clone(),
            )
            .into();
        let Some(positive_result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&positive_arg, builtin_state)?
        else {
            return Ok(None);
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                "sqrt: 0 < sqrt(x) from 0 < x".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::VerifyZeroLtSqrtFromPositiveArgBuiltinRule,
                ),
                vec![positive_result],
            ),
        )))
    }

    // Principal square root is monotone on nonnegative reals.
    // Example: from `0 <= a`, `0 <= b`, and `a <= b`, prove `sqrt(a) <= sqrt(b)`.
    pub(in crate::verification) fn verify_sqrt_monotonicity_builtin_rule(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let Some(norm) = normalize_positive_order_atomic_fact(self, atomic_fact) else {
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

    pub(in crate::verification) fn try_verify_sqrt_monotonicity(
        &mut self,
        left: Obj,
        right: Obj,
        line_file: LineFile,
        strict: bool,
        atomic_fact: &AtomicFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (Obj::Sqrt(left_sqrt), Obj::Sqrt(right_sqrt)) = (&left, &right) else {
            return Ok(None);
        };
        let zero: Obj = Number::new("0".to_string()).into();
        let left_arg = left_sqrt.arg.as_ref().clone();
        let right_arg = right_sqrt.arg.as_ref().clone();
        let mut subgoals: Vec<AtomicFact> = vec![
            self.new_less_equal_fact(zero.clone(), left_arg.clone(), line_file.clone())
                .into(),
            self.new_less_equal_fact(zero, right_arg.clone(), line_file.clone())
                .into(),
        ];
        if strict {
            subgoals.push(self.new_less_fact(left_arg, right_arg, line_file).into());
        } else {
            subgoals.push(
                self.new_less_equal_fact(left_arg, right_arg, line_file)
                    .into(),
            );
        }

        let Some(step_results) = self.verify_builtin_rule_premises(&subgoals, builtin_state)?
        else {
            return Ok(None);
        };

        let reason = if strict {
            "sqrt: sqrt(a) < sqrt(b) from 0 <= a, 0 <= b, and a < b"
        } else {
            "sqrt: sqrt(a) <= sqrt(b) from 0 <= a, 0 <= b, and a <= b"
        };
        Ok(Some(ProveFactResult::from(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                atomic_fact.clone().into(),
                reason.to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifySqrtMonotonicity,
                ),
                step_results,
            ),
        )))
    }
}
