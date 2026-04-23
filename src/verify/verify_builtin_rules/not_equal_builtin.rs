use crate::prelude::*;
use crate::verify::verify_number_in_standard_set::is_integer_after_simplification;

impl Runtime {
    pub fn _verify_not_equal_fact_with_builtin_rules(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        let left_obj = &not_equal_fact.left;
        let right_obj = &not_equal_fact.right;

        match (
            self.resolve_obj_to_number(left_obj),
            self.resolve_obj_to_number(right_obj),
        ) {
            (Some(left_number), Some(right_number)) => {
                if left_number.normalized_value != right_number.normalized_value {
                    return Ok(
                        (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            not_equal_fact.clone().into(),
                            "calculation".to_string(),
                            Vec::new(),
                        ))
                        .into(),
                    );
                }
            }
            _ => {}
        }

        if let (Obj::ListSet(left_ls), Obj::ListSet(right_ls)) = (left_obj, right_obj) {
            if left_ls.list.len() != right_ls.list.len() {
                return Ok(
                    (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                        not_equal_fact.clone().into(),
                        "list_set_different_length".to_string(),
                        Vec::new(),
                    ))
                    .into(),
                );
            }
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_from_known_strict_order(not_equal_fact)?
        {
            return Ok(verified_result);
        }

        if let Some(verified_result) =
            self.try_verify_not_equal_pow_from_base_nonzero(not_equal_fact, verify_state)?
        {
            return Ok(verified_result);
        }

        match self
            .try_verify_not_equal_fact_when_zero_and_binary_arithmetic_reduces_by_operand_facts(
                not_equal_fact,
                verify_state,
            )? {
            Some(verified_result) => return Ok(verified_result),
            None => {}
        }

        Ok((StmtUnknown::new()).into())
    }

    // x < y or x > y (including y < x / y > x spellings) in known facts implies x != y.
    fn try_verify_not_equal_from_known_strict_order(
        &mut self,
        not_equal_fact: &NotEqualFact,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let x = not_equal_fact.left.clone();
        let y = not_equal_fact.right.clone();
        let candidates: [AtomicFact; 4] = [
            LessFact::new(x.clone(), y.clone(), line_file.clone()).into(),
            GreaterFact::new(x.clone(), y.clone(), line_file.clone()).into(),
            LessFact::new(y.clone(), x.clone(), line_file.clone()).into(),
            GreaterFact::new(y.clone(), x.clone(), line_file.clone()).into(),
        ];
        for order_atomic in candidates {
            let sub =
                self.verify_non_equational_atomic_fact_with_known_atomic_facts(&order_atomic)?;
            if sub.is_true() {
                return Ok(Some(
                    FactualStmtSuccess::new_with_verified_by_builtin_rules(
                        not_equal_fact.clone().into(),
                        InferResult::new(),
                        "not_equal_from_known_strict_order".to_string(),
                        vec![sub],
                    )
                    .into(),
                ));
            }
        }
        Ok(None)
    }

    // a^n != 0 with literal integer exponent n, from a != 0 (known / full non-equational verify).
    fn try_verify_not_equal_pow_from_base_nonzero(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let pow = match (&not_equal_fact.left, &not_equal_fact.right) {
            (Obj::Pow(p), r) if self.obj_represents_zero_for_not_equal_builtin_rules(r) => p,
            (l, Obj::Pow(p)) if self.obj_represents_zero_for_not_equal_builtin_rules(l) => p,
            _ => return Ok(None),
        };
        let Obj::Number(exp_num) = pow.exponent.as_ref() else {
            return Ok(None);
        };
        if !is_integer_after_simplification(exp_num) {
            return Ok(None);
        }

        let base = pow.base.as_ref().clone();
        let base_neq_zero: AtomicFact = NotEqualFact::new(base, zero_obj, line_file.clone()).into();
        let mut result =
            self.verify_non_equational_atomic_fact_with_known_atomic_facts(&base_neq_zero)?;
        if !result.is_true() {
            result = self.verify_non_equational_atomic_fact(&base_neq_zero, verify_state, true)?;
        }
        if result.is_true() {
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules(
                    not_equal_fact.clone().into(),
                    InferResult::new(),
                    "not_equal_pow_from_base_nonzero".to_string(),
                    vec![result],
                )
                .into(),
            ));
        }
        Ok(None)
    }

    fn obj_represents_zero_for_not_equal_builtin_rules(self: &Self, obj: &Obj) -> bool {
        match self.resolve_obj_to_number(obj) {
            Some(number) => number.normalized_value == "0",
            None => false,
        }
    }

    fn operand_is_not_equal_to_zero_by_known_non_equational_facts(
        &mut self,
        operand: &Obj,
        line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let operand_not_equal_zero_fact =
            NotEqualFact::new(operand.clone(), zero_obj, line_file).into();
        let verify_result = self.verify_non_equational_atomic_fact_with_known_atomic_facts(
            &operand_not_equal_zero_fact,
        )?;
        Ok(verify_result.is_true())
    }

    fn both_operands_nonzero_by_known_non_equational_facts(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: LineFile,
    ) -> Result<bool, RuntimeError> {
        let left_nonzero = self.operand_is_not_equal_to_zero_by_known_non_equational_facts(
            left_operand,
            line_file.clone(),
        )?;
        if !left_nonzero {
            return Ok(false);
        }
        self.operand_is_not_equal_to_zero_by_known_non_equational_facts(right_operand, line_file)
    }

    fn both_operands_strictly_positive_by_non_equational_verify(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let zero_less_than_left =
            LessFact::new(zero_obj.clone(), left_operand.clone(), line_file.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &zero_less_than_left,
            verify_state,
        )? {
            return Ok(false);
        }
        let zero_less_than_right = LessFact::new(zero_obj, right_operand.clone(), line_file).into();
        self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &zero_less_than_right,
            verify_state,
        )
    }

    fn both_operands_strictly_negative_by_non_equational_verify(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let left_less_than_zero =
            LessFact::new(left_operand.clone(), zero_obj.clone(), line_file.clone()).into();
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &left_less_than_zero,
            verify_state,
        )? {
            return Ok(false);
        }
        let right_less_than_zero = LessFact::new(right_operand.clone(), zero_obj, line_file).into();
        self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &right_less_than_zero,
            verify_state,
        )
    }

    pub fn mul_product_negative_when_factors_have_strict_opposite_sign_by_non_equational_verify(
        &mut self,
        left_factor: &Obj,
        right_factor: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let left_less_than_zero =
            LessFact::new(left_factor.clone(), zero_obj.clone(), line_file.clone()).into();
        let zero_less_than_right =
            LessFact::new(zero_obj.clone(), right_factor.clone(), line_file.clone()).into();
        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &left_less_than_zero,
            verify_state,
        )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &zero_less_than_right,
            verify_state,
        )? {
            return Ok(true);
        }
        let zero_less_than_left =
            LessFact::new(zero_obj.clone(), left_factor.clone(), line_file.clone()).into();
        let right_less_than_zero = LessFact::new(right_factor.clone(), zero_obj, line_file).into();
        Ok(
            self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &zero_less_than_left,
                verify_state,
            )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &right_less_than_zero,
                verify_state,
            )?,
        )
    }

    fn sub_difference_nonzero_when_operands_have_strict_opposite_sign_by_non_equational_verify(
        &mut self,
        minuend: &Obj,
        subtrahend: &Obj,
        line_file: LineFile,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let zero_obj: Obj = Number::new("0".to_string()).into();
        let zero_less_than_minuend =
            LessFact::new(zero_obj.clone(), minuend.clone(), line_file.clone()).into();
        let subtrahend_less_than_zero =
            LessFact::new(subtrahend.clone(), zero_obj.clone(), line_file.clone()).into();
        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &zero_less_than_minuend,
            verify_state,
        )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &subtrahend_less_than_zero,
            verify_state,
        )? {
            return Ok(true);
        }
        let minuend_less_than_zero =
            LessFact::new(minuend.clone(), zero_obj.clone(), line_file.clone()).into();
        let zero_less_than_subtrahend =
            LessFact::new(zero_obj, subtrahend.clone(), line_file).into();
        Ok(
            self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &minuend_less_than_zero,
                verify_state,
            )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &zero_less_than_subtrahend,
                verify_state,
            )?,
        )
    }

    fn try_verify_not_equal_fact_when_zero_and_binary_arithmetic_reduces_by_operand_facts(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let line_file = not_equal_fact.line_file.clone();
        let expression_obj =
            if self.obj_represents_zero_for_not_equal_builtin_rules(&not_equal_fact.right) {
                &not_equal_fact.left
            } else if self.obj_represents_zero_for_not_equal_builtin_rules(&not_equal_fact.left) {
                &not_equal_fact.right
            } else {
                return Ok(None);
            };

        let builtin_rule_label = match expression_obj {
            Obj::Add(add) => {
                if self.both_operands_strictly_positive_by_non_equational_verify(
                    &add.left,
                    &add.right,
                    line_file.clone(),
                    verify_state,
                )? {
                    Some("add_not_equal_zero_both_operands_strictly_positive")
                } else if self.both_operands_strictly_negative_by_non_equational_verify(
                    &add.left,
                    &add.right,
                    line_file.clone(),
                    verify_state,
                )? {
                    Some("add_not_equal_zero_both_operands_strictly_negative")
                } else {
                    None
                }
            }
            Obj::Mul(mul) => {
                if self.both_operands_nonzero_by_known_non_equational_facts(
                    &mul.left,
                    &mul.right,
                    line_file.clone(),
                )? {
                    Some("mul_not_equal_zero_both_factors_nonzero_by_known_facts")
                } else if self.both_operands_strictly_positive_by_non_equational_verify(
                    &mul.left,
                    &mul.right,
                    line_file.clone(),
                    verify_state,
                )? {
                    Some("mul_not_equal_zero_both_factors_strictly_positive")
                } else if self.both_operands_strictly_negative_by_non_equational_verify(
                    &mul.left,
                    &mul.right,
                    line_file.clone(),
                    verify_state,
                )? {
                    Some("mul_not_equal_zero_both_factors_strictly_negative")
                } else {
                    None
                }
            }
            Obj::Sub(sub) => {
                if self.sub_difference_nonzero_when_operands_have_strict_opposite_sign_by_non_equational_verify(
                    &sub.left,
                    &sub.right,
                    line_file,
                    verify_state,
                )? {
                    Some("sub_not_equal_zero_operands_strict_opposite_sign")
                } else {
                    None
                }
            }
            other => {
                let zero_obj: Obj = Number::new("0".to_string()).into();
                let zero_lt_a = LessFact::new(
                    zero_obj.clone(),
                    other.clone(),
                    line_file.clone(),
                ).into();

                let final_round_verify_state = verify_state.make_final_round_state();

                if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                    &zero_lt_a,
                    &final_round_verify_state,
                )? {
                    Some("not_equal_zero_operand_strictly_positive")
                } else {
                    let a_lt_0 = LessFact::new(
                        other.clone(),
                        zero_obj,
                        line_file.clone(),
                    ).into();
                    if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                        &a_lt_0,
                        &final_round_verify_state,
                    )? {
                        Some("not_equal_zero_operand_strictly_negative")
                    } else {
                        None
                    }
                }
            }
        };

        match builtin_rule_label {
            Some(rule_label) => Ok(Some(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    not_equal_fact.clone().into(),
                    rule_label.to_string(),
                    Vec::new(),
                ))
                .into(),
            )),
            None => Ok(None),
        }
    }
}
