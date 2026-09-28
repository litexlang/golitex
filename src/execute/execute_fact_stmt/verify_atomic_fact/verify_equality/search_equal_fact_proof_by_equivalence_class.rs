use super::equivalence_class_graph::{
    equivalence_class_keys_in_adjacency, equivalence_class_path_in_adjacency,
    EquivalenceClassAdjacency,
};
use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::exec_env::known_fact_memory::ObjIR;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProofByEquivalenceClass;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    // Search: prove left = right by a cite-chain through stored generating edges.
    // Example: stored a=b and c=b ⇒ path (a,b,f1), (b,c,f2) proves a=c.
    pub fn search_equal_fact_proof_by_equivalence_class(
        &mut self,
        fact: &EqualFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProofByEquivalenceClass>> {
        Ok(self
            .equivalence_class_path(&fact.left, &fact.right)
            .map(|path| EqualFactSearchedProofByEquivalenceClass { path }))
    }

    // Oriented path across visible env-stack generating edges (BFS).
    pub fn equivalence_class_path(
        &self,
        left: &Obj,
        right: &Obj,
    ) -> Option<Vec<(Obj, Obj, FactId)>> {
        equivalence_class_path_in_adjacency(&self.visible_equivalence_class_adjacency(), left, right)
    }

    // Class keys across visible envs via generating-edge connectivity.
    pub fn equivalence_class_keys(&self, obj: &Obj) -> Vec<ObjIR> {
        equivalence_class_keys_in_adjacency(&self.visible_equivalence_class_adjacency(), obj)
    }

    pub(crate) fn visible_equivalence_class_adjacency(&self) -> EquivalenceClassAdjacency {
        let mut adjacency: EquivalenceClassAdjacency = HashMap::new();
        for env in self.execution_environments_stack.iter().rev() {
            for (key, edges) in env
                .facts
                .known_equivalence_classes
                .generating_edges
                .iter()
            {
                adjacency
                    .entry(key.clone())
                    .or_default()
                    .extend(edges.iter().cloned());
            }
        }
        adjacency
    }
}
