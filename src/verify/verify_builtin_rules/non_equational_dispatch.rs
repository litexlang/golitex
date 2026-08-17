use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_non_equational_atomic_fact_with_builtin_rules_inner(
        &mut self,
        atomic_fact: &AtomicFact,
        builtin_state: &UseBuiltinRuleVerifyState,
    ) -> Result<StmtResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(_) => unreachable!(),
            AtomicFact::NotEqualFact(not_equal_fact) => {
                self._verify_not_equal_fact_with_builtin_rules(not_equal_fact, builtin_state)
            }
            AtomicFact::FnEqualFact(fn_equal_fact) => self.verify_fn_equal_fact_with_builtin_rules(
                fn_equal_fact,
                &UseContextVerifyState::new_with_final_round(false),
            ),
            AtomicFact::FnEqualInFact(fn_equal_in_fact) => self
                .verify_fn_equal_in_fact_with_builtin_rules(
                    fn_equal_in_fact,
                    &UseContextVerifyState::new_with_final_round(false),
                ),
            AtomicFact::InFact(in_fact) => {
                self.verify_in_fact_with_builtin_rules(in_fact, builtin_state)
            }
            AtomicFact::NotInFact(not_in_fact) => {
                self.verify_not_in_fact_with_builtin_rules(not_in_fact, builtin_state)
            }
            AtomicFact::SubsetFact(subset_fact) => {
                self.verify_subset_fact_with_builtin_rules(subset_fact, builtin_state)
            }
            AtomicFact::SupersetFact(superset_fact) => {
                self.verify_superset_fact_with_builtin_rules(superset_fact, builtin_state)
            }
            AtomicFact::NotSubsetFact(not_subset_fact) => {
                self.verify_not_subset_fact_with_builtin_rules(not_subset_fact, builtin_state)
            }
            AtomicFact::NotSupersetFact(not_superset_fact) => {
                self.verify_not_superset_fact_with_builtin_rules(not_superset_fact, builtin_state)
            }
            AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                self.verify_order_atomic_fact_numeric_builtin_only(atomic_fact, builtin_state)
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
                    builtin_state,
                ),
            AtomicFact::IsFiniteSetFact(is_finite_set_fact) => self
                ._verify_is_finite_set_fact_with_builtin_rules(is_finite_set_fact, builtin_state),
            AtomicFact::NotIsFiniteSetFact(not_is_finite_set_fact) => self
                ._verify_not_is_finite_set_fact_with_builtin_rules(
                    not_is_finite_set_fact,
                    builtin_state,
                ),
            AtomicFact::IsCartFact(is_cart_fact) => {
                self._verify_is_cart_fact_with_builtin_rules(is_cart_fact, builtin_state)
            }
            AtomicFact::IsTupleFact(is_tuple_fact) => {
                self._verify_is_tuple_fact_with_builtin_rules(is_tuple_fact, builtin_state)
            }
            AtomicFact::NotIsNonemptySetFact(not_is_nonempty_set_fact) => self
                ._verify_not_is_nonempty_set_fact_with_builtin_rules(
                    not_is_nonempty_set_fact,
                    builtin_state,
                ),
            AtomicFact::NormalAtomicFact(_) | AtomicFact::NotNormalAtomicFact(_)
                if crate::verify::verify_proper_set_relations_builtin::is_builtin_proper_set_relation_fact(
                    atomic_fact,
                ) =>
            {
                self.verify_builtin_proper_set_relation_from_quantifier_free_premise(
                    atomic_fact,
                    builtin_state,
                )
            }
            _ => Ok((StmtUnknown::new()).into()),
        }
    }
}
