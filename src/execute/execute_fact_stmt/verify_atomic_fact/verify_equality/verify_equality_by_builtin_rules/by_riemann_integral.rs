//! A proved riemann_integral candidate determines the selected value.
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_atomic_except_equality::result::AtomicExceptEqualityFactKnownProof;
use crate::prelude::*;
pub struct RiemannIntegralSelectedValueProof {
    pub candidate: AtomicExceptEqualityFactKnownProof,
    pub value_equality: Box<EqualFactSearchedProof>,
}
impl Runtime {
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
