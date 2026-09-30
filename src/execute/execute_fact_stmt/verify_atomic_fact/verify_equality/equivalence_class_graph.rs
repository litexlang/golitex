use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::exec_env::known_fact_memory::ObjIR;
use crate::runtime::FactId;
use std::collections::{HashMap, HashSet, VecDeque};

pub type EquivalenceClassAdjacency = HashMap<ObjIR, Vec<(ObjIR, EqualFact)>>;

// BFS path from left to right. Empty Vec means same key (reflexive).
pub fn equivalence_class_path_in_adjacency(
    adjacency: &EquivalenceClassAdjacency,
    left: &Obj,
    right: &Obj,
) -> Option<Vec<(Obj, Obj, FactId)>> {
    let left_key = left.ir();
    let right_key = right.ir();
    if left_key == right_key {
        return Some(Vec::new());
    }

    let mut visited = HashSet::new();
    let mut parent: HashMap<ObjIR, (ObjIR, EqualFact)> = HashMap::new();
    let mut queue = VecDeque::new();
    visited.insert(left_key.clone());
    queue.push_back(left_key.clone());

    let mut found = false;
    while let Some(current) = queue.pop_front() {
        if current == right_key {
            found = true;
            break;
        }
        let Some(neighbors) = adjacency.get(&current) else {
            continue;
        };
        for (peer_key, equal_fact) in neighbors.iter() {
            if visited.contains(peer_key) {
                continue;
            }
            visited.insert(peer_key.clone());
            parent.insert(peer_key.clone(), (current.clone(), equal_fact.clone()));
            queue.push_back(peer_key.clone());
        }
    }
    if !found {
        return None;
    }

    let mut path_rev = Vec::new();
    let mut cursor = right_key;
    while cursor != left_key {
        let (prev_key, equal_fact) = parent.get(&cursor)?.clone();
        let step = orient_equality_step(&prev_key, &cursor, &equal_fact)?;
        path_rev.push(step);
        cursor = prev_key;
    }
    path_rev.reverse();
    Some(path_rev)
}

// All obj keys in the same connected component as `obj` (including itself).
pub fn equivalence_class_keys_in_adjacency(
    adjacency: &EquivalenceClassAdjacency,
    obj: &Obj,
) -> Vec<ObjIR> {
    let start = obj.ir();
    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();
    visited.insert(start.clone());
    queue.push_back(start);

    while let Some(current) = queue.pop_front() {
        let Some(neighbors) = adjacency.get(&current) else {
            continue;
        };
        for (peer_key, _) in neighbors.iter() {
            if visited.insert(peer_key.clone()) {
                queue.push_back(peer_key.clone());
            }
        }
    }
    visited.into_iter().collect()
}

fn orient_equality_step(
    from_key: &ObjIR,
    to_key: &ObjIR,
    equal_fact: &EqualFact,
) -> Option<(Obj, Obj, FactId)> {
    let left_key = equal_fact.left.ir();
    let right_key = equal_fact.right.ir();
    if from_key == &left_key && to_key == &right_key {
        Some((
            equal_fact.left.clone(),
            equal_fact.right.clone(),
            equal_fact.fact_id,
        ))
    } else if from_key == &right_key && to_key == &left_key {
        Some((
            equal_fact.right.clone(),
            equal_fact.left.clone(),
            equal_fact.fact_id,
        ))
    } else {
        None
    }
}

// Deterministic BFS in stored-edge order, with one path per exact IR key.
// These local candidates do not merge classes or create facts. The original
// object is always first, with an empty path; each later path starts there.
pub fn equivalence_class_members_with_paths_in_adjacency(
    adjacency: &EquivalenceClassAdjacency,
    obj: &Obj,
) -> Vec<(Obj, Vec<(Obj, Obj, FactId)>)> {
    let mut visited = HashSet::new();
    visited.insert(obj.ir());
    let mut members = vec![(obj.clone(), Vec::new())];
    let mut index = 0;
    while index < members.len() {
        let key = members[index].0.ir();
        if let Some(edges) = adjacency.get(&key) {
            for (peer_key, equal_fact) in edges {
                if visited.contains(peer_key) {
                    continue;
                }
                if let Some(step) = orient_equality_step(&key, peer_key, equal_fact) {
                    visited.insert(peer_key.clone());
                    let peer = step.1.clone();
                    let mut path = members[index].1.clone();
                    path.push(step);
                    members.push((peer, path));
                }
            }
        }
        index += 1;
    }
    members
}
