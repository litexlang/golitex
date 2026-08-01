use crate::prelude::*;

impl Runtime {
    pub(crate) fn verify_builtin_strategy_child(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        let direct = self
            .verify_atomic_fact_with_known_non_forall_facts_then_with_builtin_rules(atomic_fact)?;
        if direct.is_true() {
            return Ok(direct);
        }
        self.verify_atomic_fact_with_builtin_strategy(atomic_fact)
    }

    pub(crate) fn verify_atomic_fact_with_builtin_strategy(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<StmtResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(fact) => self.verify_equality_with_builtin_strategy(fact),
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
            _ => Ok(StmtUnknown::new().into()),
        }
    }
}
