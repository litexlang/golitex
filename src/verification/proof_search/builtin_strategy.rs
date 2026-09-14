//! Applies builtin proof strategies.

use crate::prelude::*;

impl Runtime {
    pub fn verify_builtin_strategy_child(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<VerifyFactResult, RuntimeError> {
        let proof = self.prove_builtin_strategy_child(atomic_fact, verify_state)?;
        self.complete_atomic_fact_proof_result(atomic_fact, proof, verify_state)
    }

    fn prove_builtin_strategy_child(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                let direct =
                    self.verify_equal_fact_with_bounded_builtin_routes(equal_fact, verify_state)?;
                if direct.is_success() {
                    return Ok(direct);
                }
                self.verify_equal_fact_with_builtin_strategy_routes(equal_fact, verify_state)
            }
            _ => {
                let direct = self.verify_atomic_except_equality_with_bounded_builtin_routes(
                    atomic_fact,
                    verify_state,
                )?;
                if direct.is_success() {
                    return Ok(direct);
                }
                self.verify_atomic_except_equality_with_builtin_strategy(
                    atomic_fact,
                    verify_state,
                )
            }
        }
    }

    pub fn verify_atomic_fact_with_builtin_strategy(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                self.verify_equal_fact_with_builtin_strategy_routes(equal_fact, verify_state)
            }
            _ => self
                .verify_atomic_except_equality_with_builtin_strategy(atomic_fact, verify_state),
        }
    }

    fn verify_equal_fact_with_builtin_strategy_routes(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        self.verify_equality_with_builtin_strategy(equal_fact, verify_state)
    }

    fn verify_atomic_except_equality_with_builtin_strategy(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<ProveFactResult, RuntimeError> {
        debug_assert!(!matches!(atomic_fact, AtomicFact::EqualFact(_)));
        let result = match atomic_fact {
            AtomicFact::InFact(fact) => {
                let numeric =
                    self.verify_numeric_carrier_with_builtin_strategy(fact, verify_state)?;
                if numeric.is_success() {
                    Ok(numeric)
                } else {
                    self.verify_set_membership_with_builtin_strategy(fact, verify_state)
                }
            }
            AtomicFact::SubsetFact(fact) => {
                self.verify_subset_with_builtin_strategy(fact, verify_state)
            }
            AtomicFact::SupersetFact(fact) => {
                let subset = self.new_subset_fact(
                    fact.right.clone(),
                    fact.left.clone(),
                    fact.line_file.clone(),
                );
                self.verify_subset_with_builtin_strategy(&subset, verify_state)
            }
            AtomicFact::IsFiniteSetFact(fact) => {
                self.verify_is_finite_set_with_builtin_strategy(fact, verify_state)
            }
            AtomicFact::IsNonemptySetFact(fact) => {
                self.verify_is_nonempty_set_with_builtin_strategy(fact, verify_state)
            }
            AtomicFact::NotEqualFact(fact) => {
                self.verify_nonzero_product_with_builtin_strategy(fact, verify_state)
            }
            AtomicFact::NotLessFact(_)
            | AtomicFact::NotGreaterFact(_)
            | AtomicFact::NotLessEqualFact(_)
            | AtomicFact::NotGreaterEqualFact(_)
            | AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                self.verify_additive_sign_with_builtin_strategy(atomic_fact, verify_state)
            }
            AtomicFact::EqualFact(_) => {
                unreachable!("equality has an owner-specific builtin strategy route")
            }
            _ => Ok(UnknownGenericStmtResult::new().into()),
        }?;
        Ok(result)
    }
}
