use crate::prelude::*;

impl Runtime {
    pub fn verify_non_equational_atomic_fact_with_builtin_rules(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<StmtResult, RuntimeError> {
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
            AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                self.verify_order_atomic_fact_numeric_builtin_only(atomic_fact)
            }
            AtomicFact::IsSetFact(is_set_fact) => Ok(
                (FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    is_set_fact.clone().into(),
                    "Every object is a set.".to_string(),
                    Vec::new(),
                ))
                .into(),
            ),
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
            AtomicFact::FnEqualInFact(fe) => {
                self.verify_fn_equal_in_fact_with_builtin_rules(fe, verify_state)
            }
            AtomicFact::FnEqualFact(fe) => {
                self.verify_fn_equal_fact_with_builtin_rules(fe, verify_state)
            }
            _ => Ok((StmtUnknown::new()).into()),
        }
    }

    pub fn non_equational_atomic_fact_holds_by_full_verify_pipeline(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<bool, RuntimeError> {
        let verify_result =
            self.verify_non_equational_atomic_fact(atomic_fact, verify_state, true)?;
        Ok(verify_result.is_true())
    }
}
