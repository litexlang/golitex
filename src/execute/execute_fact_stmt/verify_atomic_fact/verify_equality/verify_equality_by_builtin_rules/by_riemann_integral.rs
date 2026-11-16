//! A proved riemann_integral candidate determines the selected value.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::atomic_except_equality_fact_result_from_success;
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;
pub struct RiemannIntegralSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub value_equality: Box<EqualFactSearchedProof>,
}
pub struct RiemannIntegralValueStrategyProof {
    pub candidate: Box<VerifyFactResult>,
}
impl Runtime {
    pub(crate) fn search_riemann_integral_value_strategy(
        &mut self,
        goal: &EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<RiemannIntegralValueStrategyProof>> {
        for (selected, value) in [(&goal.left, &goal.right), (&goal.right, &goal.left)] {
            let Obj::IntegralOperator(IntegralOperator::Riemann(integral)) = selected else {
                continue;
            };
            let candidate = self.riemann_integral_candidate(
                *integral.function.clone(),
                *integral.lower.clone(),
                *integral.upper.clone(),
                value.clone(),
            );
            let well_defined = match self.verify_atomic_fact_well_definedness(&candidate, state)? {
                VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
                VerifyAtomicFactWellDefinedResult::Failed(_) => continue,
            };
            let Some(proof) =
                self.search_structural_riemann_integral_strategy(&candidate, state)?
            else {
                continue;
            };
            let candidate = atomic_except_equality_fact_result_from_success(
                &candidate,
                well_defined,
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(
                    AtomicExceptEqualityFactSearchProofByBuiltinStrategy::StructuralRiemannIntegral(
                        proof,
                    ),
                ),
            );
            return Ok(Some(RiemannIntegralValueStrategyProof {
                candidate: Box::new(candidate),
            }));
        }
        Ok(None)
    }

    pub(super) fn search_riemann_integral_selected_equality(
        &mut self,
        goal: &EqualFact,
    ) -> Option<RiemannIntegralSelectedValueProof> {
        for (selected, value) in [(&goal.left, &goal.right), (&goal.right, &goal.left)] {
            let Obj::IntegralOperator(IntegralOperator::Riemann(d)) = selected else {
                continue;
            };
            for known in self.known_riemann_integral_candidates() {
                let query = self.riemann_integral_candidate(
                    *d.function.clone(),
                    *d.lower.clone(),
                    *d.upper.clone(),
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
                return Some(RiemannIntegralSelectedValueProof {
                    candidate,
                    value_equality: Box::new(value_equality),
                });
            }
        }
        None
    }
}
