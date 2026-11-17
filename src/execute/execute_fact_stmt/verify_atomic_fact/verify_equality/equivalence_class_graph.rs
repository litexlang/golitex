use crate::ast::fact::EqualFact;
use crate::ast::obj::Obj;
use crate::exec_env::known_fact_memory::ObjIR;
use crate::runtime::FactId;
use std::collections::{HashMap, HashSet, VecDeque};

use super::by_they_are_the_same::helper::compound_objs_alpha_equal;
use crate::prelude::Runtime;

// Query-local traversal. Exposing a parent reopens the already reached nodes,
// since a new parent edge can connect back into an inner scope's graph.
pub(crate) struct EquivalentObjectCandidates {
    pub(crate) objects: Vec<Obj>,
    parents: Vec<Option<(usize, (Obj, Obj, FactId))>>,
    visited: HashSet<ObjIR>,
    exposed_from: usize,
    member_cursor: usize,
    env_cursor: usize,
    edge_cursor: usize,
}

impl EquivalentObjectCandidates {
    pub(crate) fn new(object: &Obj) -> Self {
        Self {
            objects: vec![object.clone()],
            parents: vec![None],
            visited: HashSet::from([object.ir()]),
            exposed_from: usize::MAX,
            member_cursor: 0,
            env_cursor: 0,
            edge_cursor: 0,
        }
    }

    pub(crate) fn next_in_scope(
        &mut self,
        runtime: &Runtime,
        exposed_from: usize,
    ) -> Option<usize> {
        let env_count = runtime.execution_environments_stack.len();
        if self.exposed_from != exposed_from {
            self.exposed_from = exposed_from;
            self.member_cursor = 0;
            self.env_cursor = env_count;
            self.edge_cursor = 0;
        }
        while self.member_cursor < self.objects.len() {
            let key = self.objects[self.member_cursor].ir();
            while self.env_cursor > exposed_from {
                let env = &runtime.execution_environments_stack[self.env_cursor - 1];
                if let Some(edges) = env
                    .facts
                    .known_equivalence_classes
                    .generating_edges
                    .get(&key)
                {
                    while self.edge_cursor < edges.len() {
                        let (peer_key, equality) = &edges[self.edge_cursor];
                        self.edge_cursor += 1;
                        if self.visited.contains(peer_key) {
                            continue;
                        }
                        let Some(step) = orient_equality_step(&key, peer_key, equality) else {
                            continue;
                        };
                        self.visited.insert(peer_key.clone());
                        self.objects.push(step.1.clone());
                        self.parents.push(Some((self.member_cursor, step)));
                        return Some(self.objects.len() - 1);
                    }
                }
                self.env_cursor -= 1;
                self.edge_cursor = 0;
            }
            self.member_cursor += 1;
            self.env_cursor = env_count;
        }
        None
    }

    pub(crate) fn path(&self, mut index: usize) -> Vec<(Obj, Obj, FactId)> {
        let mut path = Vec::new();
        while let Some((parent, step)) = &self.parents[index] {
            path.push(step.clone());
            index = *parent;
        }
        path.reverse();
        path
    }
}

// A source becomes eligible as soon as all its arguments have been reached.
// This covers every argument combination without materializing a Cartesian
// product or cloning the stored facts. Final matching still owns the proof.
pub(crate) struct EquivalentArguments {
    arguments: Vec<EquivalentObjectCandidates>,
    exposed_from: usize,
    argument_cursor: usize,
}

impl EquivalentArguments {
    pub(crate) fn new(arguments: &[&Obj], env_count: usize) -> Self {
        Self {
            arguments: arguments
                .iter()
                .map(|arg| EquivalentObjectCandidates::new(arg))
                .collect(),
            exposed_from: env_count,
            argument_cursor: 0,
        }
    }

    pub(crate) fn matches(&self, arguments: &[&Obj]) -> bool {
        self.arguments.len() == arguments.len()
            && self
                .arguments
                .iter()
                .zip(arguments)
                .all(|(reached, argument)| {
                    objects_match_directly(&reached.objects[0], argument)
                        || reached
                            .objects
                            .iter()
                            .skip(1)
                            .any(|object| object.ir() == argument.ir())
                })
    }

    pub(crate) fn advance(&mut self, runtime: &Runtime) -> bool {
        loop {
            if self.exposed_from == runtime.execution_environments_stack.len() {
                if self.exposed_from == 0 {
                    return false;
                }
                self.exposed_from -= 1;
            }
            while self.argument_cursor < self.arguments.len() {
                if self.arguments[self.argument_cursor]
                    .next_in_scope(runtime, self.exposed_from)
                    .is_some()
                {
                    return true;
                }
                self.argument_cursor += 1;
            }
            if self.exposed_from == 0 {
                return false;
            }
            self.exposed_from -= 1;
            self.argument_cursor = 0;
        }
    }
}

pub(crate) fn objects_match_directly(left: &Obj, right: &Obj) -> bool {
    match (left, right) {
        (Obj::Identifier(left), Obj::Identifier(right)) => {
            use crate::prelude::IdentifierObj;
            match (left, right) {
                (IdentifierObj::Plain { id: left, .. }, IdentifierObj::Plain { id: right, .. }) => {
                    left == right
                }
                _ => left == right,
            }
        }
        (Obj::StandardSet(left), Obj::StandardSet(right)) => left == right,
        _ => compound_objs_alpha_equal(left, right) || left.ir() == right.ir(),
    }
}

pub type EquivalenceClassAdjacency = HashMap<ObjIR, Vec<(ObjIR, EqualFact)>>;

// BFS path from left to right. Empty Vec means same key (reflexive).
pub fn equivalence_class_path_in_adjacency(
    adjacency: &EquivalenceClassAdjacency,
    left: &Obj,
    right: &Obj,
) -> Option<Vec<(Obj, Obj, FactId)>> {
    equivalence_class_path_from_neighbors(left, right, |key| {
        adjacency
            .get(key)
            .into_iter()
            .flatten()
            .map(|(peer, fact)| (peer, fact))
            .collect()
    })
}

// Borrow only visited edges. Both a query snapshot and the live, read-only
// scope stack supply exactly the same neighbor order and path certificate.
pub(super) fn equivalence_class_path_from_neighbors<'a>(
    left: &Obj,
    right: &Obj,
    neighbors: impl Fn(&ObjIR) -> Vec<(&'a ObjIR, &'a EqualFact)>,
) -> Option<Vec<(Obj, Obj, FactId)>> {
    let left_key = left.ir();
    let right_key = right.ir();
    if left_key == right_key {
        return Some(Vec::new());
    }

    let mut visited = HashSet::new();
    let mut parent: HashMap<ObjIR, (ObjIR, &EqualFact)> = HashMap::new();
    let mut queue = VecDeque::new();
    visited.insert(left_key.clone());
    queue.push_back(left_key.clone());

    let mut found = false;
    while let Some(current) = queue.pop_front() {
        if current == right_key {
            found = true;
            break;
        }
        for (peer_key, equal_fact) in neighbors(&current) {
            if visited.contains(peer_key) {
                continue;
            }
            visited.insert(peer_key.clone());
            parent.insert(peer_key.clone(), (current.clone(), equal_fact));
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
