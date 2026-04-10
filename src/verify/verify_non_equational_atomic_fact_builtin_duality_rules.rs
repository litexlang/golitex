use crate::prelude::*;
use crate::verify::verify_number_comparison_builtin_rule::{
    compare_normalized_number_str_to_zero, NumberCompareResult,
};

fn evaluated_numeric_denominator_sign_positive(den: &Obj) -> Option<bool> {
    let n = den.evaluate_to_normalized_decimal_number()?;
    match compare_normalized_number_str_to_zero(&n.normalized_value) {
        NumberCompareResult::Equal => None,
        NumberCompareResult::Greater => Some(true),
        NumberCompareResult::Less => Some(false),
    }
}

#[derive(Clone, Copy)]
enum OrderRelationForDivClear {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

impl OrderRelationForDivClear {
    fn flip(self) -> Self {
        match self {
            Self::Less => Self::Greater,
            Self::LessEqual => Self::GreaterEqual,
            Self::Greater => Self::Less,
            Self::GreaterEqual => Self::LessEqual,
        }
    }

    fn after_multiply_by_signed_denominator(self, denominator_is_positive: bool) -> Self {
        if denominator_is_positive {
            self
        } else {
            self.flip()
        }
    }

    fn to_atomic_fact(self, left: Obj, right: Obj, line_file: LineFile) -> AtomicFact {
        match self {
            Self::Less => AtomicFact::LessFact(LessFact::new(left, right, line_file)),
            Self::LessEqual => {
                AtomicFact::LessEqualFact(LessEqualFact::new(left, right, line_file))
            }
            Self::Greater => AtomicFact::GreaterFact(GreaterFact::new(left, right, line_file)),
            Self::GreaterEqual => AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                left,
                right,
                line_file,
            )),
        }
    }
}

fn order_relation_and_operands(
    atomic_fact: &AtomicFact,
) -> Option<(OrderRelationForDivClear, Obj, Obj, LineFile)> {
    match atomic_fact {
        AtomicFact::LessFact(f) => Some((
            OrderRelationForDivClear::Less,
            f.left.clone(),
            f.right.clone(),
            f.line_file.clone(),
        )),
        AtomicFact::LessEqualFact(f) => Some((
            OrderRelationForDivClear::LessEqual,
            f.left.clone(),
            f.right.clone(),
            f.line_file.clone(),
        )),
        AtomicFact::GreaterFact(f) => Some((
            OrderRelationForDivClear::Greater,
            f.left.clone(),
            f.right.clone(),
            f.line_file.clone(),
        )),
        AtomicFact::GreaterEqualFact(f) => Some((
            OrderRelationForDivClear::GreaterEqual,
            f.left.clone(),
            f.right.clone(),
            f.line_file.clone(),
        )),
        _ => None,
    }
}

fn try_build_order_fact_after_clearing_numeric_div_denominators(
    atomic_fact: &AtomicFact,
) -> Option<AtomicFact> {
    let (rel, left, right, line_file) = order_relation_and_operands(atomic_fact)?;

    if let (Obj::Div(ld), Obj::Div(rd)) = (&left, &right) {
        let left_den_pos = evaluated_numeric_denominator_sign_positive(ld.right.as_ref())?;
        let right_den_pos = evaluated_numeric_denominator_sign_positive(rd.right.as_ref())?;
        let product_positive = left_den_pos == right_den_pos;
        let rel2 = rel.after_multiply_by_signed_denominator(product_positive);
        let new_left = Obj::Mul(Mul::new(
            (*ld.left).clone(),
            (*rd.right).clone(),
        ));
        let new_right = Obj::Mul(Mul::new(
            (*ld.right).clone(),
            (*rd.left).clone(),
        ));
        return Some(rel2.to_atomic_fact(new_left, new_right, line_file));
    }

    if let Obj::Div(ld) = &left {
        if !matches!(&right, Obj::Div(_)) {
            let den_pos = evaluated_numeric_denominator_sign_positive(ld.right.as_ref())?;
            let rel2 = rel.after_multiply_by_signed_denominator(den_pos);
            let new_left = (*ld.left).clone();
            let new_right = Obj::Mul(Mul::new((*ld.right).clone(), right.clone()));
            return Some(rel2.to_atomic_fact(new_left, new_right, line_file));
        }
    }

    if let Obj::Div(rd) = &right {
        if !matches!(&left, Obj::Div(_)) {
            let den_pos = evaluated_numeric_denominator_sign_positive(rd.right.as_ref())?;
            let rel2 = rel.after_multiply_by_signed_denominator(den_pos);
            let new_left = Obj::Mul(Mul::new((*rd.right).clone(), left.clone()));
            let new_right = (*rd.left).clone();
            return Some(rel2.to_atomic_fact(new_left, new_right, line_file));
        }
    }

    None
}

impl Runtime {
    /// Verify subset by duality: `a subset b` iff `b superset a`.
    pub(crate) fn verify_subset_fact_with_builtin_rules(
        &mut self,
        subset_fact: &SubsetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        if subset_fact.left.to_string() == subset_fact.right.to_string() {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::SubsetFact(subset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ));
        }

        let converted_superset_fact = AtomicFact::SupersetFact(SupersetFact::new(
            subset_fact.right.clone(),
            subset_fact.left.clone(),
            subset_fact.line_file.clone(),
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_superset_fact,
            )?;
        if verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::SubsetFact(subset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify superset by duality: `a superset b` iff `b subset a`.
    pub(crate) fn verify_superset_fact_with_builtin_rules(
        &mut self,
        superset_fact: &SupersetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        if superset_fact.left.to_string() == superset_fact.right.to_string() {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::SupersetFact(superset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ));
        }
        let converted_subset_fact = AtomicFact::SubsetFact(SubsetFact::new(
            superset_fact.right.clone(),
            superset_fact.left.clone(),
            superset_fact.line_file.clone(),
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_subset_fact,
            )?;
        if verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::SupersetFact(superset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify `not subset` by converting to the dual `not superset`.
    pub(crate) fn verify_not_subset_fact_with_builtin_rules(
        &mut self,
        not_subset_fact: &NotSubsetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        let converted_not_superset_fact = AtomicFact::NotSupersetFact(NotSupersetFact::new(
            not_subset_fact.right.clone(),
            not_subset_fact.left.clone(),
            not_subset_fact.line_file.clone(),
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_not_superset_fact,
            )?;
        if verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::NotSubsetFact(not_subset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify `not superset` by converting to the dual `not subset`.
    pub(crate) fn verify_not_superset_fact_with_builtin_rules(
        &mut self,
        not_superset_fact: &NotSupersetFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        let converted_not_subset_fact = AtomicFact::NotSubsetFact(NotSubsetFact::new(
            not_superset_fact.right.clone(),
            not_superset_fact.left.clone(),
            not_superset_fact.line_file.clone(),
        ));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &converted_not_subset_fact,
            )?;
        if verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::NotSupersetFact(not_superset_fact.clone())),
                    "subset_superset_duality".to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    /// Verify `not (a < b)` by using `a >= b`.
    pub(crate) fn verify_not_less_fact_with_builtin_rules(
        &mut self,
        not_less_fact: &NotLessFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        let counterpart_fact = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
            not_less_fact.left.clone(),
            not_less_fact.right.clone(),
            not_less_fact.line_file.clone(),
        ));
        self.verify_duality_atomic_fact_by_known_counterpart(
            &AtomicFact::NotLessFact(not_less_fact.clone()),
            &counterpart_fact,
            "real_order_negation_duality",
        )
    }

    /// Verify `not (a > b)` by using `a <= b`.
    pub(crate) fn verify_not_greater_fact_with_builtin_rules(
        &mut self,
        not_greater_fact: &NotGreaterFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        if not_greater_fact.left.to_string() == not_greater_fact.right.to_string() {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::NotGreaterFact(not_greater_fact.clone())),
                    format!(
                        "{} = {}",
                        not_greater_fact.left.to_string(),
                        not_greater_fact.right.to_string()
                    )
                    .to_string(),
                    Vec::new(),
                ),
            ));
        }

        let counterpart_fact = AtomicFact::LessEqualFact(LessEqualFact::new(
            not_greater_fact.left.clone(),
            not_greater_fact.right.clone(),
            not_greater_fact.line_file.clone(),
        ));
        self.verify_duality_atomic_fact_by_known_counterpart(
            &AtomicFact::NotGreaterFact(not_greater_fact.clone()),
            &counterpart_fact,
            "real_order_negation_duality",
        )
    }

    pub(crate) fn verify_not_less_equal_fact_with_builtin_rules(
        &mut self,
        not_less_equal_fact: &NotLessEqualFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        if not_less_equal_fact.left.to_string() == not_less_equal_fact.right.to_string() {
            return Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::NotLessEqualFact(not_less_equal_fact.clone())),
                    format!(
                        "{} = {}",
                        not_less_equal_fact.left.to_string(),
                        not_less_equal_fact.right.to_string()
                    )
                    .to_string(),
                    Vec::new(),
                ),
            ));
        }

        let counterpart_fact = AtomicFact::GreaterFact(GreaterFact::new(
            not_less_equal_fact.left.clone(),
            not_less_equal_fact.right.clone(),
            not_less_equal_fact.line_file.clone(),
        ));
        self.verify_duality_atomic_fact_by_known_counterpart(
            &AtomicFact::NotLessEqualFact(not_less_equal_fact.clone()),
            &counterpart_fact,
            "real_order_negation_duality",
        )
    }

    pub(crate) fn verify_not_greater_equal_fact_with_builtin_rules(
        &mut self,
        not_greater_equal_fact: &NotGreaterEqualFact,
        _verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        let counterpart_fact = AtomicFact::LessFact(LessFact::new(
            not_greater_equal_fact.left.clone(),
            not_greater_equal_fact.right.clone(),
            not_greater_equal_fact.line_file.clone(),
        ));
        self.verify_duality_atomic_fact_by_known_counterpart(
            &AtomicFact::NotGreaterEqualFact(not_greater_equal_fact.clone()),
            &counterpart_fact,
            "real_order_negation_duality",
        )
    }

    fn verify_duality_atomic_fact_by_known_counterpart(
        &mut self,
        current_fact: &AtomicFact,
        counterpart_fact: &AtomicFact,
        builtin_rule_name: &str,
    ) -> Result<StmtExecResult, RuntimeError> {
        let counterpart_verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                counterpart_fact,
            )?;
        if counterpart_verify_result.is_true() {
            Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(current_fact.clone()),
                    builtin_rule_name.to_string(),
                    Vec::new(),
                ),
            ))
        } else {
            Ok(StmtExecResult::StmtUnknown(StmtUnknown::new()))
        }
    }

    fn verify_less_fact_when_left_is_mul_right_is_zero_by_opposite_sign_factors(
        &mut self,
        less_fact: &LessFact,
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
                Fact::AtomicFact(AtomicFact::LessFact(less_fact.clone())),
                "mul_opposite_signs_product_less_than_zero".to_string(),
                Vec::new(),
            ),
        )))
    }

    fn try_verify_order_fact_by_clearing_numeric_div_denominators(
        &mut self,
        current_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
        let Some(premise) = try_build_order_fact_after_clearing_numeric_div_denominators(current_fact)
        else {
            return Ok(None);
        };
        let final_state = verify_state.make_final_round_state();
        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(&premise, &final_state)? {
            Ok(Some(Self::real_order_congruence_builtin_success(
                current_fact,
                "real_order_multiply_through_numeric_div_denominator",
            )))
        } else {
            Ok(None)
        }
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
        if let Some(verified) =
            self.try_verify_order_fact_by_clearing_numeric_div_denominators(current_fact, verify_state)?
        {
            return Ok(verified);
        }
        if let AtomicFact::LessFact(less_fact) = current_fact {
            if let Some(verified_by_opposite_sign_factors) = self
                .verify_less_fact_when_left_is_mul_right_is_zero_by_opposite_sign_factors(
                    less_fact,
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
    /// Premises are checked via `non_equational_atomic_fact_holds_by_full_verify_pipeline` with
    /// [`VerifyState::make_final_round_state`] to avoid re-entering round-0 forall / definition paths.
    fn try_verify_real_order_congruence_builtin_rules(
        &mut self,
        current_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtExecResult>, RuntimeError> {
        let final_state = verify_state.make_final_round_state();
        let zero = Obj::Number(Number::new("0".to_string()));

        match current_fact {
            AtomicFact::GreaterEqualFact(f) => {
                if let (Obj::Sub(lsub), Obj::Sub(rsub)) = (&f.left, &f.right) {
                    if objs_equal_by_rational_expression_evaluation(&lsub.right, &rsub.right) {
                        let premise = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                            *lsub.left.clone(),
                            *rsub.left.clone(),
                            f.line_file.clone(),
                        ));
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_geq_subtract_same",
                            )));
                        }
                    }
                }
                if let (Obj::Sub(lsub), Obj::Sub(rsub)) = (&f.left, &f.right) {
                    if !objs_equal_by_rational_expression_evaluation(&lsub.right, &rsub.right) {
                        let premise_ge = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                            *lsub.left.clone(),
                            *rsub.left.clone(),
                            f.line_file.clone(),
                        ));
                        let premise_le = AtomicFact::LessEqualFact(LessEqualFact::new(
                            *lsub.right.clone(),
                            *rsub.right.clone(),
                            f.line_file.clone(),
                        ));
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_ge,
                            &final_state,
                        )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_le,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_geq_sub_two_sided",
                            )));
                        }
                    }
                }
                if let (Obj::Add(ladd), Obj::Add(radd)) = (&f.left, &f.right) {
                    if objs_equal_by_rational_expression_evaluation(&ladd.right, &radd.right) {
                        let premise = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                            *ladd.left.clone(),
                            *radd.left.clone(),
                            f.line_file.clone(),
                        ));
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_geq_add_same",
                            )));
                        }
                    }
                }
                if let (Obj::Add(ladd), Obj::Add(radd)) = (&f.left, &f.right) {
                    if !objs_equal_by_rational_expression_evaluation(&ladd.right, &radd.right) {
                        let premise_l = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                            *ladd.left.clone(),
                            *radd.left.clone(),
                            f.line_file.clone(),
                        ));
                        let premise_r = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                            *ladd.right.clone(),
                            *radd.right.clone(),
                            f.line_file.clone(),
                        ));
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_l,
                            &final_state,
                        )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_r,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_geq_add_two_sided",
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
                            let premise_d = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                                *ldm.left.clone(),
                                zero.clone(),
                                f.line_file.clone(),
                            ));
                            if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                                &premise_xy,
                                &final_state,
                            )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                                &premise_d,
                                &final_state,
                            )? {
                                return Ok(Some(Self::real_order_congruence_builtin_success(
                                    current_fact,
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
                            &final_state,
                        )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_d_nonpos,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_geq_mul_nonpos",
                            )));
                        }
                    }
                }
            }
            AtomicFact::LessEqualFact(f) => {
                if let (Obj::Add(ladd), Obj::Add(radd)) = (&f.left, &f.right) {
                    if objs_equal_by_rational_expression_evaluation(&ladd.right, &radd.right) {
                        let premise = AtomicFact::LessEqualFact(LessEqualFact::new(
                            *ladd.left.clone(),
                            *radd.left.clone(),
                            f.line_file.clone(),
                        ));
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_leq_add_same",
                            )));
                        }
                    }
                }
                if let (Obj::Add(ladd), Obj::Add(radd)) = (&f.left, &f.right) {
                    if !objs_equal_by_rational_expression_evaluation(&ladd.right, &radd.right) {
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
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_l,
                            &final_state,
                        )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_r,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_leq_add_two_sided",
                            )));
                        }
                    }
                }
                if let (Obj::Sub(lsub), Obj::Sub(rsub)) = (&f.left, &f.right) {
                    if objs_equal_by_rational_expression_evaluation(&lsub.right, &rsub.right) {
                        let premise = AtomicFact::LessEqualFact(LessEqualFact::new(
                            *lsub.left.clone(),
                            *rsub.left.clone(),
                            f.line_file.clone(),
                        ));
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_leq_subtract_same",
                            )));
                        }
                    }
                }
                if let (Obj::Sub(lsub), Obj::Sub(rsub)) = (&f.left, &f.right) {
                    if !objs_equal_by_rational_expression_evaluation(&lsub.right, &rsub.right) {
                        let premise_ge = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                            *lsub.right.clone(),
                            *rsub.right.clone(),
                            f.line_file.clone(),
                        ));
                        let premise_le = AtomicFact::LessEqualFact(LessEqualFact::new(
                            *lsub.left.clone(),
                            *rsub.left.clone(),
                            f.line_file.clone(),
                        ));
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_ge,
                            &final_state,
                        )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_le,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_leq_sub_reversed_two_sided",
                            )));
                        }
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
                                &final_state,
                            )? {
                                return Ok(Some(Self::real_order_congruence_builtin_success(
                                    current_fact,
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
                        let premise_d_nonneg = AtomicFact::GreaterEqualFact(GreaterEqualFact::new(
                            *ldm.left.clone(),
                            zero.clone(),
                            f.line_file.clone(),
                        ));
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise,
                            &final_state,
                        )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise_d_nonneg,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_leq_mul_nonneg",
                            )));
                        }
                    }
                }
            }
            AtomicFact::LessFact(f) => {
                if let (Obj::Add(ladd), Obj::Add(radd)) = (&f.left, &f.right) {
                    if objs_equal_by_rational_expression_evaluation(&ladd.right, &radd.right) {
                        let premise = AtomicFact::LessFact(LessFact::new(
                            *ladd.left.clone(),
                            *radd.left.clone(),
                            f.line_file.clone(),
                        ));
                        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                            &premise,
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
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
                            &final_state,
                        )? {
                            return Ok(Some(Self::real_order_congruence_builtin_success(
                                current_fact,
                                "real_order_congruence_lt_subtract_same",
                            )));
                        }
                    }
                }
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
