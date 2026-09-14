use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::execute::execute_fact_stmt::cache_search_proof::CacheSearchProof;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_cache(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CacheSearchProof>> {
        let _ = verify_state;
        if matches!(fact, AtomicFact::EqualFact(_)) {
            return Ok(None);
        }
        Ok(self.search_atomic_fact_proof_by_cache(fact))
    }
}
