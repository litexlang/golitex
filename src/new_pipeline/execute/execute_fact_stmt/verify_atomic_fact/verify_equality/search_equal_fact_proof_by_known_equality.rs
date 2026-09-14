use super::known_equality_graph::{
    equality_class_keys_in_adjacency, equality_path_in_adjacency, EqualityAdjacency,
};
use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::exec_env::known_fact_memory::ObjInternalRepresentation;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProofByKnownEquality;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    // Search: prove left = right by a cite-chain through stored equality edges.
    // Example: stored a=b and c=b ⇒ path (a,b,f1), (b,c,f2) proves a=c.
    pub fn search_equal_fact_proof_by_known_equality(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProofByKnownEquality>> {
        let _ = verify_state;
        Ok(self
            .known_equality_path(&fact.left, &fact.right)
            .map(|path| EqualFactSearchedProofByKnownEquality { path }))
    }

    // Oriented path across visible env-stack generating edges (BFS).
    pub fn known_equality_path(&self, left: &Obj, right: &Obj) -> Option<Vec<(Obj, Obj, FactId)>> {
        equality_path_in_adjacency(&self.visible_equality_adjacency(), left, right)
    }

    // Class keys across visible envs via generating-edge connectivity.
    // Per-env `class_members` Rc lists are maintained on store for local class
    // sharing; cross-env closure still comes from the merged edge graph.
    pub fn known_equality_class_keys(&self, obj: &Obj) -> Vec<ObjInternalRepresentation> {
        equality_class_keys_in_adjacency(&self.visible_equality_adjacency(), obj)
    }

    fn visible_equality_adjacency(&self) -> EqualityAdjacency {
        let mut adjacency: EqualityAdjacency = HashMap::new();
        for env in self.execution_environments_stack.iter().rev() {
            for (key, edges) in env.facts.known_equality.generating_edges.iter() {
                adjacency
                    .entry(key.clone())
                    .or_default()
                    .extend(edges.iter().cloned());
            }
        }
        adjacency
    }
}
