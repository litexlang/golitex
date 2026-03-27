use crate::error::VerifyError;
use crate::execute::Runtime;
use crate::fact::IsTupleFact;
use crate::fact::{
    AtomicFact, Fact, GreaterFact, IsNonemptySetFact, LessFact, NotEqualFact, NotGreaterEqualFact,
    NotGreaterFact, NotLessEqualFact, NotLessFact,
};
use crate::fact::{IsCartFact, IsFiniteSetFact};
use crate::infer::InferResult;
use crate::obj::{Number, Obj};
use crate::result::FactVerifiedByBuiltinRules;
use crate::result::NonErrStmtExecResult;
use crate::result::StmtUnknown;
use crate::verify::VerifyState;

impl Runtime {
    pub fn verify_non_equational_atomic_fact_with_builtin_rules(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match atomic_fact {
            AtomicFact::EqualFact(_) => unreachable!(),
            AtomicFact::NotEqualFact(not_equal_fact) => {
                self._verify_not_equal_fact_with_builtin_rules(not_equal_fact, verify_state)
            }
            AtomicFact::InFact(in_fact) => {
                self.verify_in_fact_with_builtin_rules(in_fact, verify_state)
            }
            AtomicFact::SubsetFact(subset_fact) => {
                self.verify_subset_fact_with_builtin_rules(subset_fact, verify_state)
            }
            AtomicFact::SupersetFact(superset_fact) => {
                self.verify_superset_fact_with_builtin_rules(superset_fact, verify_state)
            }
            AtomicFact::NotSubsetFact(not_subset_fact) => {
                self.verify_not_subset_fact_with_builtin_rules(not_subset_fact, verify_state)
            }
            AtomicFact::NotSupersetFact(not_superset_fact) => {
                self.verify_not_superset_fact_with_builtin_rules(not_superset_fact, verify_state)
            }
            AtomicFact::NotLessFact(not_less_fact) => {
                self.verify_not_less_fact_with_builtin_rules(not_less_fact, verify_state)
            }
            AtomicFact::NotGreaterFact(not_greater_fact) => {
                self.verify_not_greater_fact_with_builtin_rules(not_greater_fact, verify_state)
            }
            AtomicFact::NotLessEqualFact(not_less_equal_fact) => self
                .verify_not_less_equal_fact_with_builtin_rules(not_less_equal_fact, verify_state),
            AtomicFact::NotGreaterEqualFact(not_greater_equal_fact) => self
                .verify_not_greater_equal_fact_with_builtin_rules(
                    not_greater_equal_fact,
                    verify_state,
                ),
            AtomicFact::LessFact(less_fact) => {
                let current_fact = AtomicFact::LessFact(less_fact.clone());
                let counterpart_fact = AtomicFact::NotGreaterEqualFact(NotGreaterEqualFact::new(
                    less_fact.left.clone(),
                    less_fact.right.clone(),
                    less_fact.line_file,
                ));
                self.verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
                    &current_fact,
                    &counterpart_fact,
                )
            }
            AtomicFact::GreaterFact(greater_fact) => {
                let current_fact = AtomicFact::GreaterFact(greater_fact.clone());
                let counterpart_fact = AtomicFact::NotLessEqualFact(NotLessEqualFact::new(
                    greater_fact.left.clone(),
                    greater_fact.right.clone(),
                    greater_fact.line_file,
                ));
                self.verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
                    &current_fact,
                    &counterpart_fact,
                )
            }
            AtomicFact::LessEqualFact(less_equal_fact) => {
                let current_fact = AtomicFact::LessEqualFact(less_equal_fact.clone());
                let counterpart_fact = AtomicFact::NotGreaterFact(NotGreaterFact::new(
                    less_equal_fact.left.clone(),
                    less_equal_fact.right.clone(),
                    less_equal_fact.line_file,
                ));
                self.verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
                    &current_fact,
                    &counterpart_fact,
                )
            }
            AtomicFact::GreaterEqualFact(greater_equal_fact) => {
                let current_fact = AtomicFact::GreaterEqualFact(greater_equal_fact.clone());
                let counterpart_fact = AtomicFact::NotLessFact(NotLessFact::new(
                    greater_equal_fact.left.clone(),
                    greater_equal_fact.right.clone(),
                    greater_equal_fact.line_file,
                ));
                self.verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
                    &current_fact,
                    &counterpart_fact,
                )
            }
            AtomicFact::IsSetFact(is_set_fact) => Ok(
                NonErrStmtExecResult::FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::IsSetFact(is_set_fact.clone())),
                    "Every object is a set.".to_string(),
                    InferResult::new(),
                )),
            ),
            AtomicFact::RestrictFact(restrict_fact) => {
                self.verify_restrict_fact_with_builtin_rules(restrict_fact, verify_state)
            }
            AtomicFact::IsNonemptySetFact(is_nonempty_set_fact) => self
                ._verify_is_nonempty_set_fact_with_builtin_rules(
                    is_nonempty_set_fact,
                    verify_state,
                ),
            AtomicFact::IsFiniteSetFact(is_finite_set_fact) => {
                self._verify_is_finite_set_fact_with_builtin_rules(is_finite_set_fact, verify_state)
            }
            AtomicFact::IsCartFact(is_cart_fact) => {
                self._verify_is_cart_fact_with_builtin_rules(is_cart_fact, verify_state)
            }
            AtomicFact::IsTupleFact(is_tuple_fact) => {
                self._verify_is_tuple_fact_with_builtin_rules(is_tuple_fact, verify_state)
            }
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    fn _verify_not_equal_fact_with_builtin_rules(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let left_obj = &not_equal_fact.left;
        let right_obj = &not_equal_fact.right;

        match (
            self.get_known_normalized_calculated_value_for_obj(left_obj),
            self.get_known_normalized_calculated_value_for_obj(right_obj),
        ) {
            (Some(left_number), Some(right_number)) => {
                if left_number.normalized_value != right_number.normalized_value {
                    return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                        FactVerifiedByBuiltinRules::new(
                            Fact::AtomicFact(AtomicFact::NotEqualFact(not_equal_fact.clone())),
                            "calculation".to_string(),
                            InferResult::new(),
                        ),
                    ));
                }
            }
            _ => {}
        }

        match self
            .try_verify_not_equal_fact_when_zero_and_binary_arithmetic_reduces_by_operand_facts(
                not_equal_fact,
                verify_state,
            )? {
            Some(verified_result) => return Ok(verified_result),
            None => {}
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }

    fn obj_represents_zero_for_not_equal_builtin_rules(self: &Self, obj: &Obj) -> bool {
        match self.get_known_normalized_calculated_value_for_obj(obj) {
            Some(number) => number.normalized_value == "0",
            None => false,
        }
    }

    fn operand_is_not_equal_to_zero_by_known_non_equational_facts(
        &mut self,
        operand: &Obj,
        line_file: (usize, usize),
    ) -> Result<bool, VerifyError> {
        let zero_obj = Obj::Number(Number::new("0".to_string()));
        let operand_not_equal_zero_fact =
            AtomicFact::NotEqualFact(NotEqualFact::new(operand.clone(), zero_obj, line_file));
        let verify_result = self
            .verify_non_equational_atomic_fact_with_known_atomic_non_equational_facts(
                &operand_not_equal_zero_fact,
            )?;
        Ok(verify_result.is_true())
    }

    fn both_operands_nonzero_by_known_non_equational_facts(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: (usize, usize),
    ) -> Result<bool, VerifyError> {
        let left_nonzero = self
            .operand_is_not_equal_to_zero_by_known_non_equational_facts(left_operand, line_file)?;
        if !left_nonzero {
            return Ok(false);
        }
        self.operand_is_not_equal_to_zero_by_known_non_equational_facts(right_operand, line_file)
    }

    fn non_equational_atomic_fact_holds_by_full_verify_pipeline(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<bool, VerifyError> {
        let verify_result = self.verify_non_equational_atomic_fact(atomic_fact, verify_state)?;
        Ok(verify_result.is_true())
    }

    fn both_operands_strictly_positive_by_non_equational_verify(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: (usize, usize),
        verify_state: &VerifyState,
    ) -> Result<bool, VerifyError> {
        let zero_obj = Obj::Number(Number::new("0".to_string()));
        let left_greater_than_zero = AtomicFact::GreaterFact(GreaterFact::new(
            left_operand.clone(),
            zero_obj.clone(),
            line_file,
        ));
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &left_greater_than_zero,
            verify_state,
        )? {
            return Ok(false);
        }
        let right_greater_than_zero =
            AtomicFact::GreaterFact(GreaterFact::new(right_operand.clone(), zero_obj, line_file));
        self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &right_greater_than_zero,
            verify_state,
        )
    }

    fn both_operands_strictly_negative_by_non_equational_verify(
        &mut self,
        left_operand: &Obj,
        right_operand: &Obj,
        line_file: (usize, usize),
        verify_state: &VerifyState,
    ) -> Result<bool, VerifyError> {
        let zero_obj = Obj::Number(Number::new("0".to_string()));
        let left_less_than_zero = AtomicFact::LessFact(LessFact::new(
            left_operand.clone(),
            zero_obj.clone(),
            line_file,
        ));
        if !self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &left_less_than_zero,
            verify_state,
        )? {
            return Ok(false);
        }
        let right_less_than_zero =
            AtomicFact::LessFact(LessFact::new(right_operand.clone(), zero_obj, line_file));
        self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &right_less_than_zero,
            verify_state,
        )
    }

    fn sub_difference_nonzero_when_operands_have_strict_opposite_sign_by_non_equational_verify(
        &mut self,
        minuend: &Obj,
        subtrahend: &Obj,
        line_file: (usize, usize),
        verify_state: &VerifyState,
    ) -> Result<bool, VerifyError> {
        let zero_obj = Obj::Number(Number::new("0".to_string()));
        let minuend_greater_than_zero = AtomicFact::GreaterFact(GreaterFact::new(
            minuend.clone(),
            zero_obj.clone(),
            line_file,
        ));
        let subtrahend_less_than_zero = AtomicFact::LessFact(LessFact::new(
            subtrahend.clone(),
            zero_obj.clone(),
            line_file,
        ));
        if self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &minuend_greater_than_zero,
            verify_state,
        )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
            &subtrahend_less_than_zero,
            verify_state,
        )? {
            return Ok(true);
        }
        let minuend_less_than_zero =
            AtomicFact::LessFact(LessFact::new(minuend.clone(), zero_obj.clone(), line_file));
        let subtrahend_greater_than_zero =
            AtomicFact::GreaterFact(GreaterFact::new(subtrahend.clone(), zero_obj, line_file));
        Ok(
            self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &minuend_less_than_zero,
                verify_state,
            )? && self.non_equational_atomic_fact_holds_by_full_verify_pipeline(
                &subtrahend_greater_than_zero,
                verify_state,
            )?,
        )
    }

    fn try_verify_not_equal_fact_when_zero_and_binary_arithmetic_reduces_by_operand_facts(
        &mut self,
        not_equal_fact: &NotEqualFact,
        verify_state: &VerifyState,
    ) -> Result<Option<NonErrStmtExecResult>, VerifyError> {
        let line_file = not_equal_fact.line_file;
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
                    line_file,
                    verify_state,
                )? {
                    Some("add_not_equal_zero_both_operands_strictly_positive")
                } else if self.both_operands_strictly_negative_by_non_equational_verify(
                    &add.left,
                    &add.right,
                    line_file,
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
                    line_file,
                )? {
                    Some("mul_not_equal_zero_both_factors_nonzero_by_known_facts")
                } else if self.both_operands_strictly_positive_by_non_equational_verify(
                    &mul.left,
                    &mul.right,
                    line_file,
                    verify_state,
                )? {
                    Some("mul_not_equal_zero_both_factors_strictly_positive")
                } else if self.both_operands_strictly_negative_by_non_equational_verify(
                    &mul.left,
                    &mul.right,
                    line_file,
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
            _ => None,
        };

        match builtin_rule_label {
            Some(rule_label) => Ok(Some(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::NotEqualFact(not_equal_fact.clone())),
                    rule_label.to_string(),
                    InferResult::new(),
                ),
            ))),
            None => Ok(None),
        }
    }

    fn _verify_is_nonempty_set_fact_with_builtin_rules(
        &mut self,
        is_nonempty_set_fact: &IsNonemptySetFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match &is_nonempty_set_fact.set {
            Obj::NPosObj(_)
            | Obj::NObj(_)
            | Obj::QObj(_)
            | Obj::RObj(_)
            | Obj::RNz(_)
            | Obj::ZNz(_)
            | Obj::QNz(_)
            | Obj::QPos(_)
            | Obj::RPos(_)
            | Obj::RNeg(_)
            | Obj::ZNeg(_)
            | Obj::QNeg(_)
            | Obj::ZObj(_) => Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::IsNonemptySetFact(is_nonempty_set_fact.clone())),
                    "standard_nonempty_set".to_string(),
                    InferResult::new(),
                ),
            )),
            Obj::ListSet(_) => Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::IsNonemptySetFact(is_nonempty_set_fact.clone())),
                    "list_set_nonempty".to_string(),
                    InferResult::new(),
                ),
            )),
            Obj::Cart(cart) => {
                for arg_obj in &cart.args {
                    let is_nonempty_set_result = self
                        .verify_non_equational_atomic_fact_with_builtin_rules(
                            &AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                                *arg_obj.clone(),
                                is_nonempty_set_fact.line_file,
                            )),
                            _verify_state,
                        )?;

                    if is_nonempty_set_result.is_unknown() {
                        return Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()));
                    }
                }

                // verified by objects in cart are all nonempty sets
                Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                    FactVerifiedByBuiltinRules::new(
                        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(
                            is_nonempty_set_fact.clone(),
                        )),
                        "cart_nonempty_set".to_string(),
                        InferResult::new(),
                    ),
                ))
            }
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    fn _verify_is_finite_set_fact_with_builtin_rules(
        &mut self,
        is_finite_set_fact: &IsFiniteSetFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match &is_finite_set_fact.set {
            Obj::ListSet(_) => Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                FactVerifiedByBuiltinRules::new(
                    Fact::AtomicFact(AtomicFact::IsFiniteSetFact(is_finite_set_fact.clone())),
                    "list_set_finite".to_string(),
                    InferResult::new(),
                ),
            )),
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    fn _verify_is_cart_fact_with_builtin_rules(
        &mut self,
        is_cart_fact: &IsCartFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match &is_cart_fact.set {
            Obj::Cart(_) => {
                return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                    FactVerifiedByBuiltinRules::new(
                        Fact::AtomicFact(AtomicFact::IsCartFact(is_cart_fact.clone())),
                        "any `cart` object is a cart".to_string(),
                        InferResult::new(),
                    ),
                ));
            }
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    fn _verify_is_tuple_fact_with_builtin_rules(
        &mut self,
        is_tuple_fact: &IsTupleFact,
        _verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match &is_tuple_fact.set {
            Obj::Tuple(_) => {
                return Ok(NonErrStmtExecResult::FactVerifiedByBuiltinRules(
                    FactVerifiedByBuiltinRules::new(
                        Fact::AtomicFact(AtomicFact::IsTupleFact(is_tuple_fact.clone())),
                        "any `cart_dim` object is a cart_dim".to_string(),
                        InferResult::new(),
                    ),
                ));
            }
            _ => Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }
}
