//! Derived, constructor-directed lookup for forall equality conclusions.
//! Only real source cites leave this index; a token hit is never proof evidence.

mod helper;

use helper::{append_pattern, object_views, Token};
use crate::ast::fact::{EqualFact, ForallConclusionLocation};
use crate::ast::obj::Obj;
use crate::exec_env::{ForallConclusionCite, ObjIR};
use crate::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::equivalence_class_graph::EquivalenceClassAdjacency;
use crate::runtime::{FactId, IdentifierId};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum CiteKey {
    Direct(FactId, usize),
    And(FactId, usize, usize),
    Chain(FactId, usize, usize),
}

#[derive(Clone, Default)]
struct IndexNode {
    edges: HashMap<Token, usize>,
    entries: Vec<usize>,
    instantiated_exits: Vec<(Token, usize)>,
}

#[derive(Clone)]
struct IndexedConclusion {
    cite: ForallConclusionCite,
    tokens: Vec<Token>,
    instantiated_skips: Vec<(usize, usize)>,
}

#[derive(Clone)]
pub struct ForallEqualityIndex {
    nodes: Vec<IndexNode>,
    entries: Vec<IndexedConclusion>,
    cite_to_entry: HashMap<CiteKey, usize>,
}

impl Default for ForallEqualityIndex {
    fn default() -> Self {
        Self::new()
    }
}

impl ForallEqualityIndex {
    pub fn new() -> Self {
        Self {
            nodes: vec![IndexNode::default()],
            entries: Vec::new(),
            cite_to_entry: HashMap::new(),
        }
    }

    pub fn record(
        &mut self,
        equal: &EqualFact,
        parameters: &[IdentifierId],
        cite: ForallConclusionCite,
    ) {
        let parameters: HashSet<_> = parameters.iter().copied().collect();
        let mut tokens = Vec::new();
        let mut seen = HashSet::new();
        let mut instantiated_skips = Vec::new();
        append_pattern(
            &equal.left,
            &parameters,
            &mut seen,
            &mut tokens,
            &mut instantiated_skips,
        );
        append_pattern(
            &equal.right,
            &parameters,
            &mut seen,
            &mut tokens,
            &mut instantiated_skips,
        );
        self.insert(cite, tokens, instantiated_skips);
    }

    pub fn merge_from(&mut self, child: &Self) {
        for entry in &child.entries {
            self.insert(
                entry.cite.clone(),
                entry.tokens.clone(),
                entry.instantiated_skips.clone(),
            );
        }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
    pub fn cite(&self, index: usize) -> &ForallConclusionCite {
        &self.entries[index].cite
    }

    // Replacement uniqueness has two bare parameter endpoints. This exact
    // index branch avoids enumerating unrelated equality source statements.
    pub fn parameter_pair_cites(&self) -> Vec<&ForallConclusionCite> {
        let Some(left) = self.nodes[0].edges.get(&Token::Parameter) else {
            return Vec::new();
        };
        let Some(right) = self.nodes[*left].edges.get(&Token::Parameter) else {
            return Vec::new();
        };
        self.nodes[*right]
            .entries
            .iter()
            .map(|index| &self.entries[*index].cite)
            .collect()
    }

    pub fn candidates(
        &self,
        goal: &EqualFact,
        query: &mut EqualityIndexQuery,
    ) -> Vec<ForallConclusionCite> {
        let mut selected = HashSet::new();
        let mut visited = HashSet::new();
        self.walk(
            0,
            vec![goal.left.clone(), goal.right.clone()],
            query,
            &mut visited,
            &mut selected,
        );
        let mut selected: Vec<_> = selected.into_iter().collect();
        selected.sort_unstable();
        selected
            .into_iter()
            .map(|index| self.entries[index].cite.clone())
            .collect()
    }

    fn insert(
        &mut self,
        cite: ForallConclusionCite,
        tokens: Vec<Token>,
        instantiated_skips: Vec<(usize, usize)>,
    ) {
        let key = cite_key(&cite);
        if self.cite_to_entry.contains_key(&key) {
            return;
        }
        let entry_index = self.entries.len();
        let mut node = 0;
        let mut path = vec![node];
        for token in &tokens {
            node = match self.nodes[node].edges.get(token).copied() {
                Some(next) => next,
                None => {
                    let next = self.nodes.len();
                    self.nodes.push(IndexNode::default());
                    self.nodes[node].edges.insert(token.clone(), next);
                    next
                }
            };
            path.push(node);
        }
        for &(start, end) in &instantiated_skips {
            let exit = (tokens[start].clone(), path[end]);
            if !self.nodes[path[start]].instantiated_exits.contains(&exit) {
                self.nodes[path[start]].instantiated_exits.push(exit);
            }
        }
        self.nodes[node].entries.push(entry_index);
        self.cite_to_entry.insert(key, entry_index);
        self.entries.push(IndexedConclusion {
            cite,
            tokens,
            instantiated_skips,
        });
    }

    fn walk(
        &self,
        node: usize,
        objects: Vec<Obj>,
        query: &mut EqualityIndexQuery,
        visited: &mut HashSet<(usize, Vec<ObjIR>)>,
        selected: &mut HashSet<usize>,
    ) {
        if !visited.insert((node, objects.iter().map(Obj::ir).collect())) {
            return;
        }
        let Some((object, rest)) = objects.split_first() else {
            selected.extend(self.nodes[node].entries.iter().copied());
            return;
        };
        if let Some(next) = self.nodes[node].edges.get(&Token::Parameter) {
            self.walk(*next, rest.to_vec(), query, visited, selected);
        }
        if self.nodes[node].edges.len()
            == usize::from(self.nodes[node].edges.contains_key(&Token::Parameter))
        {
            return;
        }
        let structure_token = query.views(object)[0].0.clone();
        for (pattern_token, exit) in &self.nodes[node].instantiated_exits {
            if *pattern_token != structure_token {
                self.walk(*exit, rest.to_vec(), query, visited, selected);
            }
        }
        for variant in query.variants(object) {
            for (token, children) in query.views(&variant) {
                let mut tokens = vec![token.clone()];
                if let Token::Node(constructor, arity) = token {
                    tokens.push(Token::RigidNode(constructor, arity));
                }
                for token in tokens {
                    if let Some(next) = self.nodes[node].edges.get(&token) {
                        let mut remaining = children.clone();
                        remaining.extend_from_slice(rest);
                        self.walk(*next, remaining, query, visited, selected);
                    }
                }
            }
        }
    }
}

// Read-only alias discovery is local to one query and its visible env snapshot.
// It does not invoke truth search, infer facts or keep a Runtime cache.
pub struct EqualityIndexQuery<'a> {
    adjacencies: Vec<&'a EquivalenceClassAdjacency>,
    variants: HashMap<ObjIR, Vec<Obj>>,
    views: HashMap<ObjIR, Vec<(Token, Vec<Obj>)>>,
}

impl<'a> EqualityIndexQuery<'a> {
    pub fn new(adjacencies: Vec<&'a EquivalenceClassAdjacency>) -> Self {
        Self {
            adjacencies,
            variants: HashMap::new(),
            views: HashMap::new(),
        }
    }

    fn views(&mut self, object: &Obj) -> Vec<(Token, Vec<Obj>)> {
        let key = object.ir();
        self.views
            .entry(key)
            .or_insert_with(|| object_views(object))
            .clone()
    }

    fn variants(&mut self, object: &Obj) -> Vec<Obj> {
        let key = object.ir();
        if let Some(variants) = self.variants.get(&key) {
            return variants.clone();
        }
        let mut queue: VecDeque<_> = vec![(key.clone(), object.clone())].into_iter().collect();
        let mut seen = HashSet::new();
        let mut out = vec![object.clone()];
        while let Some((current, value)) = queue.pop_front() {
            if !seen.insert(current.clone()) {
                continue;
            }
            // Follow only stored IR edges. Pairwise binder comparison belongs
            // to the authoritative matcher, not whole-graph alias discovery.
            if current != key {
                out.push(value);
            }
            for adjacency in &self.adjacencies {
                if let Some(edges) = adjacency.get(&current) {
                    for (next, fact) in edges {
                        if seen.contains(next) {
                            continue;
                        }
                        let peer = if fact.left.ir() == *next {
                            &fact.left
                        } else {
                            &fact.right
                        };
                        queue.push_back((next.clone(), peer.clone()));
                    }
                }
            }
        }
        self.variants.insert(key, out.clone());
        out
    }
}

fn cite_key(cite: &ForallConclusionCite) -> CiteKey {
    match &cite.location {
        ForallConclusionLocation::DirectThenFact(loc) => {
            CiteKey::Direct(cite.fact_id, loc.then_fact_index)
        }
        ForallConclusionLocation::AndFactComponent(loc) => {
            CiteKey::And(cite.fact_id, loc.then_fact_index, loc.component_index)
        }
        ForallConclusionLocation::ChainFactComponent(loc) => {
            CiteKey::Chain(cite.fact_id, loc.then_fact_index, loc.component_index)
        }
    }
}

#[cfg(test)]
#[path = "../../tests/unit/execute/forall_equality_index/tests.rs"]
mod tests;
