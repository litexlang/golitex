use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Both callers have already established object WD. This phase does not
    // consume builtin or strategy fuel, and preserves the selected proof route.
    pub(in crate::execute) fn search_atomic_except_equality_fact_proof_by_known(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        if let Some(proof) =
            self.search_atomic_except_equality_fact_proof_by_known_atomic_fact(fact, verify_state)?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByKnownAtomicFact(proof),
            ));
        }
        Ok(self
            .search_atomic_except_equality_fact_proof_by_known_special_property(fact)
            .map(AtomicExceptEqualityFactSearchedProof::ByKnownSpecialProperty))
    }
}
