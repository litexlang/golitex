use super::order_div_clear::try_build_order_fact_after_clearing_numeric_div_denominators;
use super::order_normalize::normalize_positive_order_atomic_fact;
use crate::prelude::*;

impl Runtime {
    // Builtin: if right is 0 and left is u*v with u,v strictly opposite sign, then u*v < 0.
    // Recording label: mul_opposite_signs_product_less_than_zero.
    fn verify_less_fact_when_left_is_mul_right_is_zero_by_opposite_sign_factors(
        &mut self,
        less_fact: &LessFact,
        recorded_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
        let right_is_zero = match self.resolve_obj_to_number(&less_fact.right) {
            Some(number) => number.normalized_value == "0",
            None => false,
        };
        if !right_is_zero {
            return Ok(None);
        }
        let mul = match &less_fact.left {
            Obj::Mul(mul) => mul,
            _ => return Ok(None),
        };
        if !self
            .mul_product_negative_when_factors_have_strict_opposite_sign_by_non_equational_verify(
                &mul.left,
                &mul.right,
                less_fact.line_file.clone(),
                verify_state,
            )?
        {
            return Ok(None);
        }
        Ok(Some(StmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                Fact::AtomicFact(recorded_fact.clone()),
                "mul_opposite_signs_product_less_than_zero".to_string(),
                Vec::new(),
            ),
        )))
    }

    fn try_real_order_congruence_less_equal_cases(
        &mut self,
        f: &LessEqualFact,
        display_fact: &AtomicFact,
        zero: &Obj,
        final_state: &VerifyState,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
        if let (Obj::Add(ladd), Obj::Add(radd)) = (&f.left, &f.right) {
            let premise_l = AtomicFact::LessEqualFact(LessEqualFact::new(
                *ladd.left.clone(),
                *radd.left.clone(),
                f.line_file.clone(),
            ));
            let premise_r = AtomicFact::LessEqualFact(LessEqualFact::new(
                *ladd.right.clone(),
                *radd.right.clone(),
                f.line_file.clone(),
            ));
            let left_ok = self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &premise_l,
                final_state,
            )?;
            let right_by_pipeline = self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &premise_r,
                final_state,
            )?;
            let right_summands_order_as_leq = right_by_pipeline
                || objs_equal_by_rational_expression_evaluation(&ladd.right, &radd.right);
            if left_ok && right_summands_order_as_leq {
                let rule_label = if right_by_pipeline {
                    "real_order_congruence_leq_add_two_sided"
                } else {
                    "real_order_congruence_leq_add_same"
                };
                return Ok(Some(Self::real_order_congruence_builtin_success(
                    display_fact,
                    rule_label,
                )));
            }
        }
        if let (Obj::Sub(lsub), Obj::Sub(rsub)) = (&f.left, &f.right) {
            let premise_subtrahends = AtomicFact::LessEqualFact(LessEqualFact::new(
                *rsub.right.clone(),
                *lsub.right.clone(),
                f.line_file.clone(),
            ));
            let premise_minuends = AtomicFact::LessEqualFact(LessEqualFact::new(
                *lsub.left.clone(),
                *rsub.left.clone(),
                f.line_file.clone(),
            ));
            let left_ok = self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &premise_minuends,
                final_state,
            )?;
            let right_by_pipeline = self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &premise_subtrahends,
                final_state,
            )?;
            let subtrahends_order_as_leq = right_by_pipeline
                || objs_equal_by_rational_expression_evaluation(&lsub.right, &rsub.right);
            if left_ok && subtrahends_order_as_leq {
                let rule_label = if right_by_pipeline {
                    "real_order_congruence_leq_sub_reversed_two_sided"
                } else {
                    "real_order_congruence_leq_subtract_same"
                };
                return Ok(Some(Self::real_order_congruence_builtin_success(
                    display_fact,
                    rule_label,
                )));
            }
        }
        if let (Obj::Mul(ldm), Obj::Mul(rdm)) = (&f.left, &f.right) {
            if objs_equal_by_rational_expression_evaluation(&ldm.left, &rdm.left) {
                let d = &*ldm.left;
                if self
                    .resolve_obj_to_number(d)
                    .is_some_and(|n| n.normalized_value == "-1")
                {
                    let premise = AtomicFact::LessEqualFact(LessEqualFact::new(
                        *rdm.right.clone(),
                        *ldm.right.clone(),
                        f.line_file.clone(),
                    ));
                    if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                        &premise,
                        final_state,
                    )? {
                        return Ok(Some(Self::real_order_congruence_builtin_success(
                            display_fact,
                            "real_order_congruence_leq_negate_mul_minus_one",
                        )));
                    }
                }
            }
        }
        if let (Obj::Mul(ldm), Obj::Mul(rdm)) = (&f.left, &f.right) {
            if objs_equal_by_rational_expression_evaluation(&ldm.left, &rdm.left) {
                let premise = AtomicFact::LessEqualFact(LessEqualFact::new(
                    *ldm.right.clone(),
                    *rdm.right.clone(),
                    f.line_file.clone(),
                ));
                let premise_d_nonneg_as_le = AtomicFact::LessEqualFact(LessEqualFact::new(
                    zero.clone(),
                    *ldm.left.clone(),
                    f.line_file.clone(),
                ));
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &premise,
                    final_state,
                )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &premise_d_nonneg_as_le,
                    final_state,
                )? {
                    return Ok(Some(Self::real_order_congruence_builtin_success(
                        display_fact,
                        "real_order_congruence_leq_mul_nonneg",
                    )));
                }
            }
        }
        if let (Obj::Sub(lsub), Obj::Sub(rsub)) = (&f.left, &f.right) {
            if let (Obj::Mul(ldm), Obj::Mul(rdm)) = (&*lsub.right, &*rsub.right) {
                if objs_equal_by_rational_expression_evaluation(&lsub.left, &rsub.left)
                    && objs_equal_by_rational_expression_evaluation(&ldm.left, &rdm.left)
                {
                    let premise_xy = AtomicFact::LessEqualFact(LessEqualFact::new(
                        *rdm.right.clone(),
                        *lsub.left.clone(),
                        f.line_file.clone(),
                    ));
                    let premise_d_as_le = AtomicFact::LessEqualFact(LessEqualFact::new(
                        zero.clone(),
                        *ldm.left.clone(),
                        f.line_file.clone(),
                    ));
                    if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                        &premise_xy,
                        final_state,
                    )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                        &premise_d_as_le,
                        final_state,
                    )? {
                        return Ok(Some(Self::real_order_congruence_builtin_success(
                            display_fact,
                            "real_order_congruence_geq_y_minus_d_linear",
                        )));
                    }
                }
            }
        }
        if let (Obj::Mul(ldm), Obj::Mul(rdm)) = (&f.left, &f.right) {
            if objs_equal_by_rational_expression_evaluation(&ldm.left, &rdm.left) {
                let premise_ord = AtomicFact::LessEqualFact(LessEqualFact::new(
                    *ldm.right.clone(),
                    *rdm.right.clone(),
                    f.line_file.clone(),
                ));
                let premise_d_nonpos = AtomicFact::LessEqualFact(LessEqualFact::new(
                    *ldm.left.clone(),
                    zero.clone(),
                    f.line_file.clone(),
                ));
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &premise_ord,
                    final_state,
                )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &premise_d_nonpos,
                    final_state,
                )? {
                    return Ok(Some(Self::real_order_congruence_builtin_success(
                        display_fact,
                        "real_order_congruence_geq_mul_nonpos",
                    )));
                }
            }
        }
        Ok(None)
    }

    fn try_real_order_congruence_strict_less_cases(
        &mut self,
        f: &LessFact,
        display_fact: &AtomicFact,
        final_state: &VerifyState,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
        if let (Obj::Add(ladd), Obj::Add(radd)) = (&f.left, &f.right) {
            if objs_equal_by_rational_expression_evaluation(&ladd.right, &radd.right) {
                let premise = AtomicFact::LessFact(LessFact::new(
                    *ladd.left.clone(),
                    *radd.left.clone(),
                    f.line_file.clone(),
                ));
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &premise,
                    final_state,
                )? {
                    return Ok(Some(Self::real_order_congruence_builtin_success(
                        display_fact,
                        "real_order_congruence_lt_add_same",
                    )));
                }
            }
        }
        if let (Obj::Sub(lsub), Obj::Sub(rsub)) = (&f.left, &f.right) {
            if objs_equal_by_rational_expression_evaluation(&lsub.right, &rsub.right) {
                let premise = AtomicFact::LessFact(LessFact::new(
                    *lsub.left.clone(),
                    *rsub.left.clone(),
                    f.line_file.clone(),
                ));
                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &premise,
                    final_state,
                )? {
                    return Ok(Some(Self::real_order_congruence_builtin_success(
                        display_fact,
                        "real_order_congruence_lt_subtract_same",
                    )));
                }
            }
        }
        Ok(None)
    }

    fn try_verify_order_fact_by_clearing_numeric_div_denominators(
        &mut self,
        current_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
        let final_state = verify_state.make_final_round_state();
        if let Some(premise) =
            try_build_order_fact_after_clearing_numeric_div_denominators(current_fact)
        {
            if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&premise, &final_state)?
            {
                return Ok(Some(Self::real_order_congruence_builtin_success(
                    current_fact,
                    "real_order_multiply_through_numeric_div_denominator",
                )));
            }
        }
        if let Some(premise) = self.try_build_order_fact_after_clearing_div_denominators_with_verified_signs(
            current_fact,
            &final_state,
        )? {
            if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&premise, &final_state)?
            {
                return Ok(Some(Self::real_order_congruence_builtin_success(
                    current_fact,
                    "real_order_multiply_through_div_denominator_via_sign_facts",
                )));
            }
        }
        Ok(None)
    }

    /// Verify order facts by either direct number calculation or negation duality.
    pub(crate) fn verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
        &mut self,
        current_fact: &AtomicFact,
        counterpart_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        let number_compare_result = self.verify_number_comparison_builtin_rule(current_fact);
        if let Some(true) = number_compare_result {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(current_fact.clone()),
                    "number comparison".to_string(),
                    Vec::new(),
                ),
            ));
        }
        if let Some(verified) = self.try_verify_order_fact_by_clearing_numeric_div_denominators(
            current_fact,
            verify_state,
        )? {
            return Ok(verified);
        }
        if let Some(AtomicFact::LessFact(less_fact)) =
            normalize_positive_order_atomic_fact(current_fact)
        {
            if let Some(verified_by_opposite_sign_factors) = self
                .verify_less_fact_when_left_is_mul_right_is_zero_by_opposite_sign_factors(
                    &less_fact,
                    current_fact,
                    verify_state,
                )?
            {
                return Ok(verified_by_opposite_sign_factors);
            }
        }
        if let Some(verified) =
            self.try_verify_real_order_congruence_builtin_rules(current_fact, verify_state)?
        {
            return Ok(verified);
        }
        self.verify_duality_atomic_fact_by_known_counterpart(
            current_fact,
            counterpart_fact,
            "real_order_negation_duality",
        )
    }

    /// Builtin real-linearity / congruence rules (same shape as `know` order facts in examples).
    fn try_verify_real_order_congruence_builtin_rules(
        &mut self,
        current_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
        let final_state = verify_state.make_final_round_state();
        let zero = Obj::Number(Number::new("0".to_string()));

        match current_fact {
            AtomicFact::GreaterEqualFact(f) => {
                return self.try_real_order_congruence_less_equal_cases(
                    &LessEqualFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()),
                    current_fact,
                    &zero,
                    &final_state,
                );
            }
            AtomicFact::LessEqualFact(f) => {
                return self.try_real_order_congruence_less_equal_cases(
                    f,
                    current_fact,
                    &zero,
                    &final_state,
                );
            }
            AtomicFact::GreaterFact(f) => {
                return self.try_real_order_congruence_strict_less_cases(
                    &LessFact::new(f.right.clone(), f.left.clone(), f.line_file.clone()),
                    current_fact,
                    &final_state,
                );
            }
            AtomicFact::LessFact(f) => {
                return self.try_real_order_congruence_strict_less_cases(
                    f,
                    current_fact,
                    &final_state,
                );
            }
            _ => {}
        }

        Ok(None)
    }

    fn real_order_congruence_builtin_success(
        current_fact: &AtomicFact,
        label: &str,
    ) -> StmtExecResult {
        StmtExecResult::FactualStmtSuccess(
            FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                Fact::AtomicFact(current_fact.clone()),
                label.to_string(),
                Vec::new(),
            ),
        )
    }
}
