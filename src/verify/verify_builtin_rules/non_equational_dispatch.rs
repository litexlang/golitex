use crate::prelude::*;

impl Runtime {
    pub fn verify_non_equational_atomic_fact_with_builtin_rules(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtExecResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(_) => unreachable!(),
            AtomicFact::NotEqualFact(not_equal_fact) => {
                self._verify_not_equal_fact_with_builtin_rules(not_equal_fact, verify_state)
            }
            AtomicFact::InFact(in_fact) => {
                self.verify_in_fact_with_builtin_rules(in_fact, verify_state)
            }
            AtomicFact::NotInFact(not_in_fact) => {
                self.verify_not_in_fact_with_builtin_rules(not_in_fact, verify_state)
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
                    less_fact.line_file.clone(),
                ));
                self.verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
                    &current_fact,
                    &counterpart_fact,
                    verify_state,
                )
            }
            AtomicFact::GreaterFact(greater_fact) => {
                let current_fact = AtomicFact::GreaterFact(greater_fact.clone());
                let counterpart_fact = AtomicFact::NotLessEqualFact(NotLessEqualFact::new(
                    greater_fact.left.clone(),
                    greater_fact.right.clone(),
                    greater_fact.line_file.clone(),
                ));
                self.verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
                    &current_fact,
                    &counterpart_fact,
                    verify_state,
                )
            }
            AtomicFact::LessEqualFact(less_equal_fact) => {
                if less_equal_fact.left.to_string() == less_equal_fact.right.to_string() {
                    return Ok(StmtExecResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            Fact::AtomicFact(AtomicFact::LessEqualFact(less_equal_fact.clone())),
                            "less_equal_fact_equal".to_string(),
                            Vec::new(),
                        ),
                    ));
                }
                let current_fact = AtomicFact::LessEqualFact(less_equal_fact.clone());
                let counterpart_fact = AtomicFact::NotGreaterFact(NotGreaterFact::new(
                    less_equal_fact.left.clone(),
                    less_equal_fact.right.clone(),
                    less_equal_fact.line_file.clone(),
                ));
                self.verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
                    &current_fact,
                    &counterpart_fact,
                    verify_state,
                )
            }
            AtomicFact::GreaterEqualFact(greater_equal_fact) => {
                if greater_equal_fact.left.to_string() == greater_equal_fact.right.to_string() {
                    return Ok(StmtExecResult::FactualStmtSuccess(
                        FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                            Fact::AtomicFact(AtomicFact::GreaterEqualFact(
                                greater_equal_fact.clone(),
                            )),
                            "greater_equal_fact_equal".to_string(),
                            Vec::new(),
                        ),
                    ));
                }
                let current_fact = AtomicFact::GreaterEqualFact(greater_equal_fact.clone());
                let counterpart_fact = AtomicFact::NotLessFact(NotLessFact::new(
                    greater_equal_fact.left.clone(),
                    greater_equal_fact.right.clone(),
                    greater_equal_fact.line_file.clone(),
                ));
                self.verify_order_or_negation_fact_with_builtin_duality_and_number_compare(
                    &current_fact,
                    &counterpart_fact,
                    verify_state,
                )
            }
            AtomicFact::IsSetFact(is_set_fact) => Ok(StmtExecResult::FactualStmtSuccess(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    Fact::AtomicFact(AtomicFact::IsSetFact(is_set_fact.clone())),
                    "Every object is a set.".to_string(),
                    Vec::new(),
                ),
            )),
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
            AtomicFact::NotIsNonemptySetFact(not_is_nonempty_set_fact) => self
                ._verify_not_is_nonempty_set_fact_with_builtin_rules(
                    not_is_nonempty_set_fact,
                    verify_state,
                ),
            _ => Ok(StmtExecResult::StmtUnknown(StmtUnknown::new())),
        }
    }

    pub(crate) fn non_equational_atomic_fact_holds_by_full_verify_pipeline(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let verify_result = self.verify_non_equational_atomic_fact(atomic_fact, verify_state)?;
        Ok(verify_result.is_true())
    }
}
