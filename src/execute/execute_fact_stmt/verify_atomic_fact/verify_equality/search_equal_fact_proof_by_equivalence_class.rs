use super::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use super::equivalence_class_graph::{
    equivalence_class_keys_in_adjacency, equivalence_class_members_with_paths_in_adjacency,
    equivalence_class_path_in_adjacency, EquivalenceClassAdjacency,
};
use super::result::{EqualityViaPeersProof, KnownEqualityPathProof, KnownEqualityAlphaEndpointsProof, PeerEqualitySuccess};
use super::well_defined_result::VerifyEqualFactWellDefinedResult;
use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::exec_env::known_fact_memory::ObjIR;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProofByEquivalenceClass;
use crate::execute::execute_fact_stmt::{VerifyState};
use crate::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    // One class-search stage: first cite an existing path, then try one cheap
    // bridge between peers. Example: a=b, d=c and a new proof of b=d imply a=c.
    // All candidates and citations come from one read-only visible graph snapshot.
    pub fn search_equal_fact_proof_by_equivalence_class(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProofByEquivalenceClass>> {
        let adjacency = self.visible_equivalence_class_adjacency();
        if let Some(path) = equivalence_class_path_in_adjacency(&adjacency, &fact.left, &fact.right)
        {
            return Ok(Some(KnownEqualityPathProof::new(path).into()));
        }

        // BFS lists include the original endpoint at index 0. Try left-only,
        // right-only, then both sides; never repeat the already-tried goal pair.
        let left = equivalence_class_members_with_paths_in_adjacency(&adjacency, &fact.left);
        let right = equivalence_class_members_with_paths_in_adjacency(&adjacency, &fact.right);
        let left_only = (1..left.len()).map(|i| (i, 0));
        let right_only = (1..right.len()).map(|j| (0, j));
        let both = (1..left.len()).flat_map(|i| (1..right.len()).map(move |j| (i, j)));
        let child_state = verify_state.capped_at(
            crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule,
        );
        for (i, j) in left_only.chain(right_only).chain(both) {
            let mut bridge_fact = fact.clone();
            bridge_fact.fact_id = self.global_ids.allocate_fact_id();
            bridge_fact.left = left[i].0.clone();
            bridge_fact.right = right[j].0.clone();
            let Some(bridge) = self.verify_equality_class_peer(bridge_fact, child_state.clone())?
            else {
                continue;
            };
            // Right BFS runs goal.right -> peer; the certificate needs peer ->
            // goal.right. Reverse both the edge order and every edge direction.
            let right_path = right[j]
                .1
                .iter()
                .rev()
                .map(|(from, to, id)| (to.clone(), from.clone(), *id))
                .collect();
            return Ok(Some(
                EqualityViaPeersProof::new(
                    KnownEqualityPathProof::new(left[i].1.clone()),
                    bridge,
                    KnownEqualityPathProof::new(right_path),
                )
                .into(),
            ));
        }
        Ok(search_alpha_endpoints(&adjacency, fact))
    }

    // A bridge verifies WD and searches with the shared ceiling <= BuiltinRule.
    // It cannot start another peer stage or restore permission through WD/infer.
    // No successful bridge is stored in the caller's knowledge base.
    fn verify_equality_class_peer(
        &mut self,
        fact: EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<PeerEqualitySuccess>> {
        let well_defined_proof =
            match self.verify_equal_fact_well_definedness(&fact, state.clone())? {
                VerifyEqualFactWellDefinedResult::Success(proof) => proof,
                VerifyEqualFactWellDefinedResult::Failed(_) => return Ok(None),
            };
        Ok(self.search_equal_fact_proof(&fact, state)?.map(|proof| {
            PeerEqualitySuccess::new(fact, well_defined_proof, proof)
        }))
    }

    // Oriented path across visible env-stack generating edges (BFS).
    pub fn equivalence_class_path(
        &self,
        left: &Obj,
        right: &Obj,
    ) -> Option<Vec<(Obj, Obj, FactId)>> {
        equivalence_class_path_in_adjacency(
            &self.visible_equivalence_class_adjacency(),
            left,
            right,
        )
    }

    // Class keys across visible envs via generating-edge connectivity.
    pub fn equivalence_class_keys(&self, obj: &Obj) -> Vec<ObjIR> {
        equivalence_class_keys_in_adjacency(&self.visible_equivalence_class_adjacency(), obj)
    }

    pub(crate) fn visible_equivalence_class_adjacency(&self) -> EquivalenceClassAdjacency {
        let mut adjacency: EquivalenceClassAdjacency = HashMap::new();
        for env in self.execution_environments_stack.iter().rev() {
            for (key, edges) in env.facts.known_equivalence_classes.generating_edges.iter() {
                adjacency
                    .entry(key.clone())
                    .or_default()
                    .extend(edges.iter().cloned());
            }
        }
        adjacency
    }
}

pub(crate) fn search_alpha_endpoints(adjacency: &EquivalenceClassAdjacency, fact: &EqualFact) -> Option<EqualFactSearchedProofByEquivalenceClass> {
    // Stored binder IDs can differ from a freshly parsed goal's IDs.
    // Cite the existing equality and prove pure alpha identity on each side;
    // never normalize the knowledge graph or perform definition rewriting.
    for edges in adjacency.values() {
        for (_, cited) in edges {
        for reversed in [false, true] {
            let (left, right) = if reversed { (&cited.right, &cited.left) }
            else { (&cited.left, &cited.right) };
            // Compare borrowed objects before allocating a candidate fact. Most
            // stored edges have a different shape and cannot be alpha endpoints.
            if !same_or_alpha_objects(&fact.left, left) || !same_or_alpha_objects(&fact.right, right) {
                continue;
            }
            let mut endpoint = fact.clone();
            endpoint.right = left.clone();
            let Some(left_identity) = search_equal_fact_proof_by_they_are_the_same(&endpoint) else { continue; };
            endpoint.left = fact.right.clone();
            endpoint.right = right.clone();
            let Some(right_identity) = search_equal_fact_proof_by_they_are_the_same(&endpoint) else { continue; };
            return Some(EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(
            KnownEqualityAlphaEndpointsProof { cited: cited.clone(), reversed, left_identity, right_identity }
            ));
        }
        }
    }
    // Multi-edge version: the finite classes contain only stored objects.
    // Compare their endpoints structurally, without WD or any proof-search call.
    let left = equivalence_class_members_with_paths_in_adjacency(adjacency, &fact.left);
    let right = equivalence_class_members_with_paths_in_adjacency(adjacency, &fact.right);
    for (l, lpath) in &left {
        for (r, rpath) in &right {
            if lpath.is_empty() && rpath.is_empty() { continue; }
            if !same_or_alpha_objects(l, r) { continue; }
            let mut bridge = fact.clone();
            bridge.left = l.clone();
            bridge.right = r.clone();
            let Some(identity) = search_equal_fact_proof_by_they_are_the_same(&bridge) else { continue; };
            return Some(EqualFactSearchedProofByEquivalenceClass::AlphaPaths(
                super::result::KnownEqualityAlphaPathsProof {
                    left_path: KnownEqualityPathProof::new(lpath.clone()),
                    left: l.clone(), right: r.clone(), identity,
                    right_path: KnownEqualityPathProof::new(rpath.iter().rev()
                        .map(|(from, to, id)| (to.clone(), from.clone(), *id)).collect()),
                },
            ));
        }
    }
    None
}

fn same_or_alpha_objects(left: &Obj, right: &Obj) -> bool {
    if std::mem::discriminant(left) != std::mem::discriminant(right) { return false; }
    super::by_they_are_the_same::helper::compound_objs_alpha_equal(left, right)
        || left.ir() == right.ir()
}
