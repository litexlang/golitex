//! Subtraction recovered from known addition.

use crate::prelude::*;

impl Runtime {
    pub(super) fn try_verify_subtraction_from_known_addition(
        &mut self,
        equal_fact: &EqualFact,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        if let Some(done) =
            self.try_verify_one_subtraction_from_known_addition(equal_fact, true, builtin_state)?
        {
            return Ok(Some(done));
        }
        self.try_verify_one_subtraction_from_known_addition(equal_fact, false, builtin_state)
    }

    // Moves one addend across a known sum equality.
    // Example: from a known `a + b = c` or `b + a = c`, prove `a = c - b`.
    pub(super) fn try_verify_one_subtraction_from_known_addition(
        &mut self,
        equal_fact: &EqualFact,
        target_is_left: bool,
        builtin_state: &BuiltinRuleSearchState,
    ) -> Result<Option<ProveFactResult>, RuntimeError> {
        let (target_a, subtraction_side) = if target_is_left {
            (&equal_fact.left, &equal_fact.right)
        } else {
            (&equal_fact.right, &equal_fact.left)
        };
        let line_file = &equal_fact.line_file;
        let Obj::Sub(subtraction) = subtraction_side else {
            return Ok(None);
        };

        let candidate_sum_1: Obj =
            Add::new(target_a.clone(), subtraction.right.as_ref().clone()).into();
        let sum_fact_1 = EqualFact::new_from_refs(
            &candidate_sum_1,
            subtraction.left.as_ref(),
            line_file.clone(),
        );
        let known_sum_1 = self.verify_equal_fact_by_known_equality(&sum_fact_1);
        if known_sum_1.is_success() {
            let known_sum_1 = self.complete_fact_proof_result(
                &sum_fact_1.clone().into(),
                known_sum_1,
                builtin_state.verify_state(),
            )?;
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "equality: a = c - b from known a + b = c".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyOneSubtractionFromKnownAddition01,
                    ),
                    vec![known_sum_1],
                )
                .into(),
            ));
        }

        let candidate_sum_2: Obj =
            Add::new(subtraction.right.as_ref().clone(), target_a.clone()).into();
        let sum_fact_2 = EqualFact::new_from_refs(
            &candidate_sum_2,
            subtraction.left.as_ref(),
            line_file.clone(),
        );
        let known_sum_2 = self.verify_equal_fact_by_known_equality(&sum_fact_2);
        if known_sum_2.is_success() {
            let known_sum_2 = self.complete_fact_proof_result(
                &sum_fact_2.clone().into(),
                known_sum_2,
                builtin_state.verify_state(),
            )?;
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "equality: a = c - b from known b + a = c".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyOneSubtractionFromKnownAddition02,
                    ),
                    vec![known_sum_2],
                )
                .into(),
            ));
        }

        let premise_result = self.try_verify_builtin_rule_premise_alternatives(
            vec![vec![sum_fact_1.into()], vec![sum_fact_2.into()]],
            line_file.clone(),
            builtin_state,
        )?;
        if let Some(premise_result) = premise_result {
            return Ok(Some(
                SuccessProveFactResult::new_with_verified_by_builtin_rule_evidence_recording_stmt(
                    equal_fact.clone().into(),
                    "equality: subtraction from complete addition-order disjunction".to_string(),
                    BuiltinRuleEvidence::Uncatalogued(
                        UncataloguedBuiltinRule::TryVerifyOneSubtractionFromKnownAddition03,
                    ),
                    vec![premise_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }
}
