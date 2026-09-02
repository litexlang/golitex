//! Equality from two-sided weak order.

use crate::prelude::*;

impl Runtime {
    pub(super) fn verify_weak_order_subgoal(
        &mut self,
        greater_or_equal: &Obj,
        less_or_equal: &Obj,
        line_file: LineFile,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<VerifyFactResult>, RuntimeError> {
        let greater_equal: AtomicFact = GreaterEqualFact::new(
            greater_or_equal.clone(),
            less_or_equal.clone(),
            line_file.clone(),
        )
        .into();
        if let Some(result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&greater_equal, builtin_state)?
        {
            return Ok(Some(result));
        }

        let less_equal: AtomicFact =
            LessEqualFact::new(less_or_equal.clone(), greater_or_equal.clone(), line_file).into();
        if let Some(result) =
            self.try_verify_atomic_fact_as_builtin_rule_premise(&less_equal, builtin_state)?
        {
            return Ok(Some(result));
        }

        Ok(None)
    }

    // Equality follows from antisymmetry of the standard weak order.
    // Example: from `a >= b` and `b >= a`, prove `a = b`.
    // Membership premises in selected order builtins restrict list-set equality
    // search so that this fallback cannot recursively reopen the same goals.
    pub(super) fn try_verify_equality_from_two_sided_weak_order(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let left = &equal_fact.left;
        let right = &equal_fact.right;
        let line_file = equal_fact.line_file.clone();
        let left_in_r: AtomicFact =
            InFact::new(left.clone(), StandardSet::R.into(), line_file.clone()).into();
        let right_in_r: AtomicFact =
            InFact::new(right.clone(), StandardSet::R.into(), line_file.clone()).into();
        let left_ge_right: AtomicFact =
            GreaterEqualFact::new(left.clone(), right.clone(), line_file.clone()).into();
        let right_le_left: AtomicFact =
            LessEqualFact::new(right.clone(), left.clone(), line_file.clone()).into();
        let right_ge_left: AtomicFact =
            GreaterEqualFact::new(right.clone(), left.clone(), line_file.clone()).into();
        let left_le_right: AtomicFact =
            LessEqualFact::new(left.clone(), right.clone(), line_file.clone()).into();
        let complete_result = self.try_verify_builtin_rule_premise_alternatives(
            vec![
                vec![
                    left_in_r.clone(),
                    right_in_r.clone(),
                    left_ge_right.clone(),
                    right_ge_left.clone(),
                ],
                vec![
                    left_in_r.clone(),
                    right_in_r.clone(),
                    left_ge_right,
                    left_le_right.clone(),
                ],
                vec![
                    left_in_r.clone(),
                    right_in_r.clone(),
                    right_le_left.clone(),
                    right_ge_left,
                ],
                vec![left_in_r, right_in_r, right_le_left, left_le_right],
            ],
            line_file.clone(),
            builtin_state,
        )?;
        if let Some(complete_result) = complete_result {
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "equality from a >= b and b >= a".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyEqualityFromTwoSidedWeakOrder01,
                    ),
                    vec![complete_result],
                )
                .into(),
            ));
        }

        let Some(mut steps) = self.verify_objects_are_known_reals_in_builtin(
            &[left, right],
            &line_file,
            builtin_state,
        )?
        else {
            return Ok(None);
        };
        let Some(left_ge_right) =
            self.verify_weak_order_subgoal(left, right, line_file.clone(), builtin_state)?
        else {
            return Ok(None);
        };
        let Some(right_ge_left) =
            self.verify_weak_order_subgoal(right, left, line_file.clone(), builtin_state)?
        else {
            return Ok(None);
        };
        steps.push(left_ge_right);
        steps.push(right_ge_left);

        Ok(Some(
            SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                equal_fact.clone().into(),
                "equality from a >= b and b >= a".to_string(),
                BuiltinRuleEvidence::Uncatalogued(
                    UncataloguedBuiltinRule::TryVerifyEqualityFromTwoSidedWeakOrder02,
                ),
                steps,
            )
            .into(),
        ))
    }
}
