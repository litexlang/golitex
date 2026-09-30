use super::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use super::equivalence_class_graph::{
    equivalence_class_keys_in_adjacency, equivalence_class_members_with_paths_in_adjacency,
    equivalence_class_path_in_adjacency, EquivalenceClassAdjacency,
};
use super::result::{EqualityViaPeersProof, KnownEqualityPathProof, PeerEqualitySuccess};
use super::well_defined_result::VerifyEqualFactWellDefinedResult;
use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::exec_env::known_fact_memory::ObjIR;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProofByEquivalenceClass;
use crate::execute::execute_fact_stmt::{EqualityClassSearchMode, VerifyState};
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
        if verify_state.equality_class_search == EqualityClassSearchMode::StoredPathsOnly {
            return Ok(None);
        }

        // BFS lists include the original endpoint at index 0. Try left-only,
        // right-only, then both sides; never repeat the already-tried goal pair.
        let left = equivalence_class_members_with_paths_in_adjacency(&adjacency, &fact.left);
        let right = equivalence_class_members_with_paths_in_adjacency(&adjacency, &fact.right);
        let left_only = (1..left.len()).map(|i| (i, 0));
        let right_only = (1..right.len()).map(|j| (0, j));
        let both = (1..left.len()).flat_map(|i| (1..right.len()).map(move |j| (i, j)));
        let child_state = verify_state.for_equality_peer_comparison();
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
        Ok(None)
    }

    // A bridge verifies WD and then only identity, budgeted builtin or matching.
    // StoredPathsOnly reaches direct WD, builtin premises and matching children.
    // Binder WD retains its separate local inference entry (see VerifyState).
    // No successful bridge is stored in the caller's knowledge base.
    fn verify_equality_class_peer(
        &mut self,
        fact: EqualFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<PeerEqualitySuccess>> {
        debug_assert_eq!(
            state.equality_class_search,
            EqualityClassSearchMode::StoredPathsOnly
        );
        let well_defined_proof =
            match self.verify_equal_fact_well_definedness(&fact, state.clone())? {
                VerifyEqualFactWellDefinedResult::Success(proof) => proof,
                VerifyEqualFactWellDefinedResult::Failed(_) => return Ok(None),
            };
        if let Some(proof) = search_equal_fact_proof_by_they_are_the_same(&fact) {
            return Ok(Some(PeerEqualitySuccess::new(
                fact,
                well_defined_proof,
                proof.into(),
            )));
        }
        if state.can_use_builtin_rule_round > 0 {
            if let Some(proof) =
                self.search_equal_fact_builtin_rule(&fact, state.with_one_less_round())?
            {
                return Ok(Some(PeerEqualitySuccess::new(
                    fact,
                    well_defined_proof,
                    proof.into(),
                )));
            }
        }
        if let Some(proof) = self
            .search_equal_fact_proof_by_matching_one_arg_by_one(&fact, state.known_only_no_wd())?
        {
            return Ok(Some(PeerEqualitySuccess::new(
                fact,
                well_defined_proof,
                proof.into(),
            )));
        }
        Ok(None)
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
