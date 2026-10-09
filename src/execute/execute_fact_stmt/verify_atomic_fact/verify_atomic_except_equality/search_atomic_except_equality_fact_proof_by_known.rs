#[cfg(test)]
use crate::ast::fact::AtomicFact;
#[cfg(test)]
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
#[cfg(test)]
use crate::execute::execute_fact_stmt::VerifyState;
#[cfg(test)]
use crate::runtime::{Runtime, RuntimeResult};

#[cfg(test)]
impl Runtime {
    // Test helper for known-only search after object WD, preserving the proof route.
    pub(in crate::execute) fn search_atomic_except_equality_fact_proof_by_known(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        self.search_atomic_except_equality_fact_proof(
            fact,
            verify_state.capped_at(
                crate::execute::execute_fact_stmt::VerifyStateLevel::KnownSpecialProperty,
            ),
        )
    }
}
