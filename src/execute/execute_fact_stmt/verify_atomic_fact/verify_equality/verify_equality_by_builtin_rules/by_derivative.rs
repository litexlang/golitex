//! A proved derivative candidate determines the selected value.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::atomic_except_equality_fact_result_from_success;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;
pub struct DerivativeSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub value_equality: Box<EqualFactSearchedProof>,
}

// An already well-defined derivative selector equals a structurally proved
// candidate. Example: diff_at(square,3) followed by deriv(square,3)=6.
pub struct DerivativeValueStrategyProof {
    pub candidate: Box<VerifyFactResult>,
}

impl Runtime {
    pub(crate) fn search_derivative_value_strategy(
        &mut self,
        goal: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<DerivativeValueStrategyProof>> {
        for (selected, value) in [(&goal.left, &goal.right), (&goal.right, &goal.left)] {
            let Obj::DerivativeOperator(DerivativeOperator::AtPoint(derivative)) = selected else {
                continue;
            };
            let candidate = self.derivative_candidate(
                *derivative.function.clone(),
                *derivative.point.clone(),
                value.clone(),
            );
            let well_defined = match self.verify_atomic_fact_well_definedness(&candidate, state)? {
                VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
                VerifyAtomicFactWellDefinedResult::Failed(_) => continue,
            };
            let Some(proof) = self.search_pointwise_derivative_strategy(&candidate, state)? else {
                continue;
            };
            let candidate = atomic_except_equality_fact_result_from_success(
                &candidate,
                well_defined,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
                    AtomicExceptEqualityFactSearchProofByBuiltinStrategy::PointwiseDerivative(
                        proof,
                    ),
                ),
            );
            return Ok(Some(DerivativeValueStrategyProof {
                candidate: Box::new(candidate),
            }));
        }
        Ok(None)
    }

    pub(super) fn search_derivative_selected_equality(
        &mut self,
        goal: &EqualFact,
    ) -> Option<DerivativeSelectedValueProof> {
        for (selected, value) in [(&goal.left, &goal.right), (&goal.right, &goal.left)] {
            let Obj::DerivativeOperator(DerivativeOperator::AtPoint(d)) = selected else {
                continue;
            };
            for known in self.known_derivative_candidates() {
                let query = self.derivative_candidate(
                    *d.function.clone(),
                    *d.point.clone(),
                    known.value.clone(),
                );
                let Some(candidate) = self.lookup_known_atomic_premise(query) else {
                    continue;
                };
                let comparison = EqualFact {
                    fact_id: self.global_ids.allocate_fact_id(),
                    left: known.value,
                    right: value.clone(),
                    line_file: None,
                };
                let Some(value_equality) = self.search_equal_fact_proof_directly(&comparison)
                else {
                    continue;
                };
                return Some(DerivativeSelectedValueProof {
                    candidate,
                    value_equality: Box::new(value_equality),
                });
            }
        }
        None
    }
}
