use crate::prelude::*;
use std::collections::{HashMap, HashSet, VecDeque};

type EqualityNodeId = usize;

#[derive(Clone)]
struct KnownEqualityEntry {
    direct_proof_map: HashMap<ObjString, AtomicFact>,
    node_id: EqualityNodeId,
}

#[derive(Clone)]
struct EqualityNode {
    parent: EqualityNodeId,
    size: usize,
    members: Vec<Obj>,
}

/// One checked edge in a path through the stored equality graph.
///
/// `equality` is the original fact that justified the edge. `from` and `to`
/// record the orientation in which a compiler must use that fact.
#[derive(Clone)]
pub struct KnownEqualityProofStep {
    pub from: Obj,
    pub to: Obj,
    pub equality: EqualFact,
}

impl std::fmt::Debug for KnownEqualityProofStep {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("KnownEqualityProofStep")
            .field("from", &self.from.to_string())
            .field("to", &self.to.to_string())
            .field("equality", &self.equality.to_string())
            .finish()
    }
}

/// Equality classes indexed by alpha-normalized object keys.
///
/// Each key owns only its direct proof edges and a node id. Class membership
/// lives once at the union-find root, so extending a class does not scan and
/// rebind every key already in that class.
#[derive(Clone)]
pub struct KnownEquality {
    entries: HashMap<ObjString, KnownEqualityEntry>,
    nodes: Vec<EqualityNode>,
}

impl KnownEquality {
    pub fn new() -> Self {
        KnownEquality {
            entries: HashMap::new(),
            nodes: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn get(&self, key: &str) -> Option<(&HashMap<ObjString, AtomicFact>, &[Obj])> {
        let (_, direct_proof_map, members) = self.get_with_class_id(key)?;
        Some((direct_proof_map, members))
    }

    /// The class id is local to this store and stable until the next mutation.
    pub(crate) fn get_with_class_id(
        &self,
        key: &str,
    ) -> Option<(usize, &HashMap<ObjString, AtomicFact>, &[Obj])> {
        let entry = self.entries.get(key)?;
        let root_id = self.root_id(entry.node_id);
        Some((
            root_id,
            &entry.direct_proof_map,
            self.nodes[root_id].members.as_slice(),
        ))
    }

    pub fn iter(
        &self,
    ) -> impl Iterator<Item = (&ObjString, (&HashMap<ObjString, AtomicFact>, &[Obj]))> {
        self.entries.iter().map(|(key, entry)| {
            let root_id = self.root_id(entry.node_id);
            (
                key,
                (
                    &entry.direct_proof_map,
                    self.nodes[root_id].members.as_slice(),
                ),
            )
        })
    }

    pub fn values(&self) -> impl Iterator<Item = (&HashMap<ObjString, AtomicFact>, &[Obj])> {
        self.entries.values().map(|entry| {
            let root_id = self.root_id(entry.node_id);
            (
                &entry.direct_proof_map,
                self.nodes[root_id].members.as_slice(),
            )
        })
    }

    /// Returns an ordered proof path from `from` to `to` when the equality
    /// store contains one. This exposes the checked direct edges rather than
    /// merely reporting that both objects share a union-find class.
    pub fn proof_path(&self, from: &Obj, to: &Obj) -> Option<Vec<KnownEqualityProofStep>> {
        let from_key = obj_equality_key(from);
        let to_key = obj_equality_key(to);
        if from_key == to_key {
            return Some(Vec::new());
        }

        let mut queue = VecDeque::from([from_key.clone()]);
        let mut visited = HashSet::from([from_key.clone()]);
        let mut parents: HashMap<ObjString, (ObjString, EqualFact)> = HashMap::new();

        while let Some(current) = queue.pop_front() {
            let entry = self.entries.get(&current)?;
            for (neighbor, proof) in entry.direct_proof_map.iter() {
                let AtomicFact::EqualFact(equality) = proof else {
                    continue;
                };
                if !visited.insert(neighbor.clone()) {
                    continue;
                }
                parents.insert(neighbor.clone(), (current.clone(), equality.clone()));
                if neighbor == &to_key {
                    return Self::reconstruct_proof_path(&from_key, &to_key, parents);
                }
                queue.push_back(neighbor.clone());
            }
        }

        None
    }

    fn reconstruct_proof_path(
        from_key: &str,
        to_key: &str,
        parents: HashMap<ObjString, (ObjString, EqualFact)>,
    ) -> Option<Vec<KnownEqualityProofStep>> {
        let mut current = to_key.to_string();
        let mut reversed = Vec::new();
        while current != from_key {
            let (parent, equality) = parents.get(&current)?.clone();
            let left_key = obj_equality_key(&equality.left);
            let right_key = obj_equality_key(&equality.right);
            let (from, to) = if left_key == parent && right_key == current {
                (equality.left.clone(), equality.right.clone())
            } else if right_key == parent && left_key == current {
                (equality.right.clone(), equality.left.clone())
            } else {
                return None;
            };
            reversed.push(KnownEqualityProofStep { from, to, equality });
            current = parent;
        }
        reversed.reverse();
        Some(reversed)
    }

    pub fn store(&mut self, equality: &EqualFact) {
        let left_raw_key = equality.left.to_string();
        let right_raw_key = equality.right.to_string();
        let left_key = obj_equality_key(&equality.left);
        let right_key = obj_equality_key(&equality.right);
        if left_key == right_key {
            return;
        }

        let left_node = self.entries.get(&left_key).map(|entry| entry.node_id);
        let right_node = self.entries.get(&right_key).map(|entry| entry.node_id);
        if let (Some(left_node), Some(right_node)) = (left_node, right_node) {
            if self.root_id(left_node) == self.root_id(right_node) {
                return;
            }
        }

        let left_node = match left_node {
            Some(node_id) => node_id,
            None => self.insert_term(left_key.clone(), equality.left.clone()),
        };
        let right_node = match right_node {
            Some(node_id) => node_id,
            None => self.insert_term(right_key.clone(), equality.right.clone()),
        };

        let equality_fact: AtomicFact = equality.clone().into();
        self.entries
            .get_mut(&left_key)
            .expect("left equality term was inserted")
            .direct_proof_map
            .insert(right_key.clone(), equality_fact.clone());
        self.entries
            .get_mut(&right_key)
            .expect("right equality term was inserted")
            .direct_proof_map
            .insert(left_key.clone(), equality_fact);

        self.union(left_node, right_node);
        self.insert_raw_alias(left_raw_key, &left_key);
        self.insert_raw_alias(right_raw_key, &right_key);
    }

    fn insert_term(&mut self, key: ObjString, object: Obj) -> EqualityNodeId {
        let node_id = self.nodes.len();
        self.nodes.push(EqualityNode {
            parent: node_id,
            size: 1,
            members: vec![object],
        });
        self.entries.insert(
            key,
            KnownEqualityEntry {
                direct_proof_map: HashMap::new(),
                node_id,
            },
        );
        node_id
    }

    fn insert_raw_alias(&mut self, raw_key: ObjString, normalized_key: &str) {
        if raw_key == normalized_key {
            return;
        }
        let Some(entry) = self.entries.get(normalized_key).cloned() else {
            return;
        };
        self.entries.insert(raw_key, entry);
    }

    fn root_id(&self, mut node_id: EqualityNodeId) -> EqualityNodeId {
        while self.nodes[node_id].parent != node_id {
            node_id = self.nodes[node_id].parent;
        }
        node_id
    }

    fn union(&mut self, left_node: EqualityNodeId, right_node: EqualityNodeId) {
        let left_root = self.root_id(left_node);
        let right_root = self.root_id(right_node);
        if left_root == right_root {
            return;
        }

        let (large_root, small_root) = if self.nodes[left_root].size >= self.nodes[right_root].size
        {
            (left_root, right_root)
        } else {
            (right_root, left_root)
        };
        let small_members = std::mem::take(&mut self.nodes[small_root].members);
        self.nodes[small_root].parent = large_root;
        self.nodes[large_root].size += self.nodes[small_root].size;
        self.nodes[large_root].members.extend(small_members);
    }
}

impl Default for KnownEquality {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn named_obj(name: &str) -> Obj {
        AtomObj::Identifier(Identifier::new(name.to_string())).into()
    }

    fn equality(left: &str, right: &str) -> EqualFact {
        EqualFact::new(named_obj(left), named_obj(right), default_line_file())
    }

    #[test]
    fn equality_classes_merge_and_enumerate_from_any_member() {
        let mut known = KnownEquality::new();
        known.store(&equality("x0", "x1"));
        known.store(&equality("x2", "x3"));
        known.store(&equality("x1", "x2"));

        for key in ["x0", "x1", "x2", "x3"] {
            let (_, members) = known.get(key).expect("member must have an equality class");
            let mut member_keys = members.iter().map(obj_equality_key).collect::<Vec<_>>();
            member_keys.sort();
            assert_eq!(member_keys, vec!["x0", "x1", "x2", "x3"]);
        }
    }

    #[test]
    fn equality_class_id_is_shared_by_every_member() {
        let mut known = KnownEquality::new();
        known.store(&equality("x0", "x1"));
        known.store(&equality("x2", "x3"));

        let left_class = known.get_with_class_id("x0").unwrap().0;
        let right_class = known.get_with_class_id("x2").unwrap().0;
        assert_ne!(left_class, right_class);

        known.store(&equality("x1", "x2"));
        let merged_class = known.get_with_class_id("x0").unwrap().0;
        for key in ["x1", "x2", "x3"] {
            assert_eq!(known.get_with_class_id(key).unwrap().0, merged_class);
        }
    }

    #[test]
    fn equality_clone_is_an_independent_transaction_snapshot() {
        let mut original = KnownEquality::new();
        original.store(&equality("x0", "x1"));

        let mut snapshot = original.clone();
        snapshot.store(&equality("x1", "x2"));

        assert!(original.get("x2").is_none());
        assert_eq!(original.get("x0").unwrap().1.len(), 2);
        assert_eq!(snapshot.get("x0").unwrap().1.len(), 3);
    }

    #[test]
    fn redundant_equality_keeps_the_existing_direct_proof_forest() {
        let mut known = KnownEquality::new();
        known.store(&equality("x0", "x1"));
        known.store(&equality("x1", "x2"));
        let proof_count_before = known
            .values()
            .map(|(proofs, _)| proofs.len())
            .sum::<usize>();

        known.store(&equality("x0", "x2"));

        let proof_count_after = known
            .values()
            .map(|(proofs, _)| proofs.len())
            .sum::<usize>();
        assert_eq!(proof_count_after, proof_count_before);
    }

    #[test]
    fn equality_proof_path_preserves_edge_order_and_orientation() {
        let mut known = KnownEquality::new();
        known.store(&equality("x0", "x1"));
        known.store(&equality("x1", "x2"));

        let forward = known
            .proof_path(&named_obj("x0"), &named_obj("x2"))
            .expect("forward path");
        assert_eq!(forward.len(), 2);
        assert_eq!(forward[0].from.to_string(), "x0");
        assert_eq!(forward[0].to.to_string(), "x1");
        assert_eq!(forward[1].from.to_string(), "x1");
        assert_eq!(forward[1].to.to_string(), "x2");

        let backward = known
            .proof_path(&named_obj("x2"), &named_obj("x0"))
            .expect("backward path");
        assert_eq!(backward.len(), 2);
        assert_eq!(backward[0].from.to_string(), "x2");
        assert_eq!(backward[0].to.to_string(), "x1");
        assert_eq!(backward[1].from.to_string(), "x1");
        assert_eq!(backward[1].to.to_string(), "x0");
    }
}
