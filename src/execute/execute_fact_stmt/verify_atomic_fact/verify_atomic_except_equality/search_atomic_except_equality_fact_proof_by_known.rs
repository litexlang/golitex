use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Both callers have already established object WD. This phase does not
    // enable builtin entry or consume strategy depth, and preserves the selected proof route.
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
