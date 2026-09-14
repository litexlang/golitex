use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::display_and_ir::FactIR;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::new_pipeline::runtime::Runtime;

// Exact FactIR hit. The cache index only stores AtomicFact.
pub struct CacheSearchProof {
    pub fact: AtomicFact,
    pub cite_fact_id: FactId,
}

impl Runtime {
    // Exact FactIR hit in the current ExecEnv stack (inner scopes first).
    // Only AtomicFact is indexed; composite facts never enter this path.
    pub fn search_atomic_fact_proof_by_cache(
        &self,
        fact: &AtomicFact,
    ) -> Option<CacheSearchProof> {
        let key: FactIR = fact.ir();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some((cite_fact_id, stored)) = env.facts.lookup_atomic_by_ir(&key) {
                return Some(CacheSearchProof {
                    fact: stored.clone(),
                    cite_fact_id,
                });
            }
        }
        None
    }
}
