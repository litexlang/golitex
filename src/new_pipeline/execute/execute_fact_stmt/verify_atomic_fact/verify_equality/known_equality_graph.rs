use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::exec_env::known_fact_memory::ObjKey;
use crate::new_pipeline::runtime::FactId;
use std::collections::{HashMap, HashSet, VecDeque};

pub type EqualityAdjacency = HashMap<ObjKey, Vec<(ObjKey, EqualFact)>>;

// BFS path from left to right. Empty Vec means same key (reflexive).
pub fn equality_path_in_adjacency(
    adjacency: &EqualityAdjacency,
    left: &Obj,
    right: &Obj,
) -> Option<Vec<(Obj, Obj, FactId)>> {
    let left_key = left.internal_representation();
    let right_key = right.internal_representation();
    if left_key == right_key {
        return Some(Vec::new());
    }

    let mut visited = HashSet::new();
    let mut parent: HashMap<ObjKey, (ObjKey, EqualFact)> = HashMap::new();
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
pub fn equality_class_keys_in_adjacency(adjacency: &EqualityAdjacency, obj: &Obj) -> Vec<ObjKey> {
    let start = obj.internal_representation();
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
    from_key: &str,
    to_key: &str,
    equal_fact: &EqualFact,
) -> Option<(Obj, Obj, FactId)> {
    let left_key = equal_fact.left.internal_representation();
    let right_key = equal_fact.right.internal_representation();
    if from_key == left_key && to_key == right_key {
        Some((
            equal_fact.left.clone(),
            equal_fact.right.clone(),
            equal_fact.fact_id,
        ))
    } else if from_key == right_key && to_key == left_key {
        Some((
            equal_fact.right.clone(),
            equal_fact.left.clone(),
            equal_fact.fact_id,
        ))
    } else {
        None
    }
}
