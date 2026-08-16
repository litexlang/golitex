use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_builtin_strategy_child(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                let direct = self.verify_equal_fact_with_direct_routes(equal_fact)?;
                if direct.is_true() {
                    return Ok(direct);
                }
                self.verify_equal_fact_with_builtin_strategy_routes(equal_fact)
            }
            _ => {
                let direct =
                    self.verify_non_equational_atomic_fact_with_direct_routes(atomic_fact)?;
                if direct.is_true() {
                    return Ok(direct);
                }
                self.verify_non_equational_atomic_fact_with_builtin_strategy(atomic_fact)
            }
        }
    }

    pub(crate) fn verify_atomic_fact_with_builtin_strategy(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact_with_builtin_strategy_routes(equal_fact)
            }
            _ => self.verify_non_equational_atomic_fact_with_builtin_strategy(atomic_fact),
        }
    }

    fn verify_equal_fact_with_builtin_strategy_routes(
        &mut self,
        equal_fact: &EqualFact,
    ) -> Result<StmtResult, RuntimeError> {
        let atomic_fact: AtomicFact = equal_fact.clone().into();
        if let Some(memoized_result) = self.verify_atomic_fact_from_statement_memo(&atomic_fact) {
            return Ok(memoized_result);
        }
        let result = self.verify_equality_with_builtin_strategy(equal_fact)?;
        Ok(self.remember_successful_atomic_fact_for_statement(&atomic_fact, result))
    }

    fn verify_non_equational_atomic_fact_with_builtin_strategy(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        if let Some(memoized_result) = self.verify_atomic_fact_from_statement_memo(atomic_fact) {
            return Ok(memoized_result);
        }
        let result = match atomic_fact {
            AtomicFact::InFact(fact) => {
                let numeric = self.verify_numeric_carrier_with_builtin_strategy(fact)?;
                if numeric.is_true() {
                    Ok(numeric)
                } else {
                    self.verify_set_membership_with_builtin_strategy(fact)
                }
            }
            AtomicFact::SubsetFact(fact) => self.verify_subset_with_builtin_strategy(fact),
            AtomicFact::SupersetFact(fact) => {
                let subset = SubsetFact::new(
                    fact.right.clone(),
                    fact.left.clone(),
                    fact.line_file.clone(),
                );
                self.verify_subset_with_builtin_strategy(&subset)
            }
            AtomicFact::IsFiniteSetFact(fact) => {
                self.verify_is_finite_set_with_builtin_strategy(fact)
            }
            AtomicFact::IsNonemptySetFact(fact) => {
                self.verify_is_nonempty_set_with_builtin_strategy(fact)
            }
            AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                self.verify_additive_sign_with_builtin_strategy(atomic_fact)
            }
            AtomicFact::EqualFact(_) => {
                unreachable!("equality has an owner-specific builtin strategy route")
            }
            _ => Ok(StmtUnknown::new().into()),
        }?;
        Ok(self.remember_successful_atomic_fact_for_statement(atomic_fact, result))
    }
}
