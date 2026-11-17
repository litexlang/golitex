use super::by_they_are_the_same::search_equal_fact_proof_by_they_are_the_same;
use super::equivalence_class_graph::{
    equivalence_class_keys_in_adjacency, EquivalenceClassAdjacency, EquivalentObjectCandidates,
};
use super::result::{
    EqualityViaPeersProof, KnownEqualityAlphaEndpointsProof, KnownEqualityAlphaPathProof,
    KnownEqualityPathProof, PeerEqualitySuccess,
};
use super::well_defined_result::EqualFactWellDefinedProof;
use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::exec_env::known_fact_memory::ObjIR;
use crate::execute::execute_fact_stmt::verify_atomic_fact::EqualFactSearchedProofByEquivalenceClass;
use crate::execute::execute_fact_stmt::well_defined_results::{
    ObjWellDefinedProof, VerifyObjWellDefinedResult,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{FactId, Runtime, RuntimeResult};
use std::collections::HashMap;

impl Runtime {
    // One class-search stage: first cite an existing path, then try one cheap
    // bridge between peers. Example: a=b, d=c and a new proof of b=d imply a=c.
    // Candidates are reached lazily through current-scope edges, then parent edges.
    pub fn search_equal_fact_proof_by_equivalence_class(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProofByEquivalenceClass>> {
        if let Some(path) = self.equivalence_class_path(&fact.left, &fact.right) {
            return Ok(Some(KnownEqualityPathProof::new(path).into()));
        }

        let mut left_candidates = Vec::new();
        let mut right_candidates = Vec::new();
        let mut left_seen = std::collections::HashSet::new();
        let mut right_seen = std::collections::HashSet::new();
        // Alpha-renamed endpoints use the actual generating source. Borrow
        // sources in scope order and clone only the winning certificate.
        for env in self.execution_environments_stack.iter().rev() {
            let mut citations: Vec<_> = env
                .facts
                .known_equivalence_classes
                .generating_edges
                .values()
                .flatten()
                .map(|(_, cited)| cited)
                .collect();
            citations.sort_unstable_by_key(|cited| cited.fact_id.value());
            citations.dedup_by_key(|cited| cited.fact_id);
            for cited in citations {
                for reversed in [false, true] {
                    let (left, right) = if reversed {
                        (&cited.right, &cited.left)
                    } else {
                        (&cited.left, &cited.right)
                    };
                    let mut identity = fact.clone();
                    identity.left = left.clone();
                    identity.right = fact.left.clone();
                    let Some(left_identity) =
                        search_equal_fact_proof_by_they_are_the_same(&identity)
                    else {
                        continue;
                    };
                    identity.left = right.clone();
                    identity.right = fact.right.clone();
                    let Some(right_identity) =
                        search_equal_fact_proof_by_they_are_the_same(&identity)
                    else {
                        continue;
                    };
                    return Ok(Some(
                        EqualFactSearchedProofByEquivalenceClass::AlphaEndpoints(
                            KnownEqualityAlphaEndpointsProof {
                                cited: cited.clone(),
                                reversed,
                                left_identity,
                                right_identity,
                            },
                        ),
                    ));
                }
                for endpoint in [&cited.left, &cited.right] {
                    let mut identity = fact.clone();
                    identity.right = endpoint.clone();
                    if left_seen.insert(endpoint.ir()) {
                        identity.left = fact.left.clone();
                        if let Some(proof) = search_equal_fact_proof_by_they_are_the_same(&identity)
                        {
                            left_candidates.push((endpoint, proof));
                        }
                    }
                    if right_seen.insert(endpoint.ir()) {
                        identity.left = fact.right.clone();
                        if search_equal_fact_proof_by_they_are_the_same(&identity).is_some() {
                            right_candidates.push(endpoint);
                        }
                    }
                }
            }
        }

        for (left, left_identity) in left_candidates {
            for right in &right_candidates {
                let Some(path) = self.equivalence_class_path(left, right) else {
                    continue;
                };
                let mut identity = fact.clone();
                identity.left = (*right).clone();
                identity.right = fact.right.clone();
                let Some(right_identity) = search_equal_fact_proof_by_they_are_the_same(&identity)
                else {
                    continue;
                };
                return Ok(Some(EqualFactSearchedProofByEquivalenceClass::AlphaPath(
                    KnownEqualityAlphaPathProof {
                        left: left.clone(),
                        right: (*right).clone(),
                        left_identity,
                        path: KnownEqualityPathProof::new(path),
                        right_identity,
                    },
                )));
            }
        }

        let mut left = EquivalentObjectCandidates::new(&fact.left);
        let mut right = EquivalentObjectCandidates::new(&fact.right);
        let child_state = verify_state
            .capped_at(crate::execute::execute_fact_stmt::VerifyStateLevel::BuiltinRule);
        // All candidates share this scope and ceiling. Retain each successful
        // endpoint proof once, then move the selected pair into the bridge.
        let mut left_wd = vec![None];
        let mut right_wd = vec![None];
        for scope in (0..self.execution_environments_stack.len()).rev() {
            while let Some(i) = left.next_in_scope(self, scope) {
                left_wd.push(None);
                for j in 0..right.objects.len() {
                    if let Some(proof) = self.try_equivalent_pair(
                        fact,
                        child_state,
                        &left,
                        &right,
                        i,
                        j,
                        &mut left_wd[i],
                        &mut right_wd[j],
                    )? {
                        return Ok(Some(proof));
                    }
                }
            }
            while let Some(j) = right.next_in_scope(self, scope) {
                right_wd.push(None);
                for i in 0..left.objects.len() {
                    if let Some(proof) = self.try_equivalent_pair(
                        fact,
                        child_state,
                        &left,
                        &right,
                        i,
                        j,
                        &mut left_wd[i],
                        &mut right_wd[j],
                    )? {
                        return Ok(Some(proof));
                    }
                }
            }
        }
        Ok(None)
    }

    fn try_equivalent_pair(
        &mut self,
        fact: &EqualFact,
        state: VerifyState,
        left: &EquivalentObjectCandidates,
        right: &EquivalentObjectCandidates,
        i: usize,
        j: usize,
        left_wd: &mut Option<ObjWellDefinedProof>,
        right_wd: &mut Option<ObjWellDefinedProof>,
    ) -> RuntimeResult<Option<EqualFactSearchedProofByEquivalenceClass>> {
        let mut bridge_fact = fact.clone();
        bridge_fact.fact_id = self.global_ids.allocate_fact_id();
        bridge_fact.left = left.objects[i].clone();
        bridge_fact.right = right.objects[j].clone();
        let Some(bridge) =
            self.verify_equality_class_peer(bridge_fact, state, left_wd, right_wd)?
        else {
            return Ok(None);
        };
        let right_path = right
            .path(j)
            .into_iter()
            .rev()
            .map(|(from, to, id)| (to, from, id))
            .collect();
        Ok(Some(
            EqualityViaPeersProof::new(
                KnownEqualityPathProof::new(left.path(i)),
                bridge,
                KnownEqualityPathProof::new(right_path),
            )
            .into(),
        ))
    }

    // A bridge verifies WD and searches with the shared ceiling <= BuiltinRule.
    // It cannot start another peer stage or restore permission through WD/infer.
    // No successful bridge is stored in the caller's knowledge base.
    fn verify_equality_class_peer(
        &mut self,
        fact: EqualFact,
        state: VerifyState,
        left_wd: &mut Option<ObjWellDefinedProof>,
        right_wd: &mut Option<ObjWellDefinedProof>,
    ) -> RuntimeResult<Option<PeerEqualitySuccess>> {
        for (endpoint, retained) in [(&fact.left, &mut *left_wd), (&fact.right, &mut *right_wd)] {
            if retained.is_none() {
                match self.verify_obj_well_definedness(endpoint, state)? {
                    VerifyObjWellDefinedResult::Success(proof) => *retained = Some(proof),
                    VerifyObjWellDefinedResult::Failed { .. } => return Ok(None),
                }
            }
        }
        let Some(proof) = self.search_equal_fact_proof(&fact, state)? else {
            return Ok(None);
        };
        let well_defined_proof = EqualFactWellDefinedProof::from_children(
            self.result_detail(),
            left_wd.take().expect("checked left peer endpoint"),
            right_wd.take().expect("checked right peer endpoint"),
        )?;
        Ok(Some(PeerEqualitySuccess::new(
            fact,
            well_defined_proof,
            proof,
        )))
    }

    // Oriented path across visible env-stack generating edges (BFS).
    pub fn equivalence_class_path(
        &self,
        left: &Obj,
        right: &Obj,
    ) -> Option<Vec<(Obj, Obj, FactId)>> {
        super::equivalence_class_graph::equivalence_class_path_from_neighbors(left, right, |key| {
            self.execution_environments_stack
                .iter()
                .rev()
                .filter_map(|env| {
                    env.facts
                        .known_equivalence_classes
                        .generating_edges
                        .get(key)
                })
                .flatten()
                .map(|(peer, fact)| (peer, fact))
                .collect()
        })
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
