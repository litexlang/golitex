use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::display_and_ir::FactIR;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::new_pipeline::runtime::Runtime;

// Exact FactIR hit. Cite the stored FactId; payload lives in facts_by_id.
pub struct CacheSearchProof {
    pub cite_fact_id: FactId,
}

impl Runtime {
    // Exact FactIR hit in the current ExecEnv stack (inner scopes first).
    pub fn search_fact_proof_by_cache(&self, fact: &Fact) -> Option<CacheSearchProof> {
        let key: FactIR = fact.ir();
        for env in self.execution_environments_stack.iter().rev() {
            if let Some((cite_fact_id, _)) = env.facts.lookup_fact_by_ir(&key) {
                return Some(CacheSearchProof { cite_fact_id });
            }
        }
        None
    }

    // Atomic-only convenience over `search_fact_proof_by_cache`.
    pub fn search_atomic_fact_proof_by_cache(
        &self,
        fact: &AtomicFact,
    ) -> Option<CacheSearchProof> {
        self.search_fact_proof_by_cache(&Fact::AtomicFact(fact.clone()))
    }
}
