//! Environment-owned conclusions projected from stored universal facts.

use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

/// Search indexes for conclusions projected from exact stored universal facts.
#[derive(Clone)]
pub struct ForallConclusionMemory {
    pub atomic_with_parameterized_head:
        HashMap<(AtomicFactKey, bool), Vec<(AtomicFact, Rc<StoredForallConclusionReference>)>>,
    pub atomic_by_argument_shape: HashMap<
        (AtomicFactKey, bool),
        HashMap<ForallArgumentShape, Vec<(AtomicFact, Rc<StoredForallConclusionReference>)>>,
    >,
    pub existential: HashMap<ExistFactKey, Vec<(ExistFact, Rc<StoredForallConclusionReference>)>>,
    pub conjunction: HashMap<AndFactKey, Vec<(AndFact, Rc<StoredForallConclusionReference>)>>,
    pub disjunction: HashMap<OrFactKey, Vec<(OrFact, Rc<StoredForallConclusionReference>)>>,
}

impl ForallConclusionMemory {
    pub fn new() -> Self {
        Self {
            atomic_with_parameterized_head: HashMap::new(),
            atomic_by_argument_shape: HashMap::new(),
            existential: HashMap::new(),
            conjunction: HashMap::new(),
            disjunction: HashMap::new(),
        }
    }

    pub fn merge_from(&mut self, child: Self) {
        for (key, child_facts) in child.atomic_with_parameterized_head {
            let parent_facts = self.atomic_with_parameterized_head.entry(key).or_default();
            append_missing_atomic_pairs(parent_facts, child_facts);
        }
        for (key, child_shape_map) in child.atomic_by_argument_shape {
            let parent_shape_map = self.atomic_by_argument_shape.entry(key).or_default();
            for (shape_key, child_facts) in child_shape_map {
                let parent_facts = parent_shape_map.entry(shape_key).or_default();
                append_missing_atomic_pairs(parent_facts, child_facts);
            }
        }
        for (key, child_facts) in child.existential {
            let parent_facts = self.existential.entry(key).or_default();
            append_missing_exist_pairs(parent_facts, child_facts);
        }
        for (key, child_facts) in child.conjunction {
            let parent_facts = self.conjunction.entry(key).or_default();
            append_missing_and_pairs(parent_facts, child_facts);
        }
        for (key, child_facts) in child.disjunction {
            let parent_facts = self.disjunction.entry(key).or_default();
            append_missing_or_pairs(parent_facts, child_facts);
        }
    }
}

fn append_missing_atomic_pairs(
    parent: &mut Vec<(AtomicFact, Rc<StoredForallConclusionReference>)>,
    child: Vec<(AtomicFact, Rc<StoredForallConclusionReference>)>,
) {
    let mut seen = parent
        .iter()
        .map(|(fact, reference)| pair_key(fact.to_string(), reference))
        .collect::<HashSet<_>>();
    for (fact, reference) in child {
        if seen.insert(pair_key(fact.to_string(), &reference)) {
            parent.push((fact, reference));
        }
    }
}

fn append_missing_exist_pairs(
    parent: &mut Vec<(ExistFact, Rc<StoredForallConclusionReference>)>,
    child: Vec<(ExistFact, Rc<StoredForallConclusionReference>)>,
) {
    let mut seen = parent
        .iter()
        .map(|(fact, reference)| pair_key(fact.to_string(), reference))
        .collect::<HashSet<_>>();
    for (fact, reference) in child {
        if seen.insert(pair_key(fact.to_string(), &reference)) {
            parent.push((fact, reference));
        }
    }
}

fn append_missing_and_pairs(
    parent: &mut Vec<(AndFact, Rc<StoredForallConclusionReference>)>,
    child: Vec<(AndFact, Rc<StoredForallConclusionReference>)>,
) {
    let mut seen = parent
        .iter()
        .map(|(fact, reference)| pair_key(fact.to_string(), reference))
        .collect::<HashSet<_>>();
    for (fact, reference) in child {
        if seen.insert(pair_key(fact.to_string(), &reference)) {
            parent.push((fact, reference));
        }
    }
}

fn append_missing_or_pairs(
    parent: &mut Vec<(OrFact, Rc<StoredForallConclusionReference>)>,
    child: Vec<(OrFact, Rc<StoredForallConclusionReference>)>,
) {
    let mut seen = parent
        .iter()
        .map(|(fact, reference)| pair_key(fact.to_string(), reference))
        .collect::<HashSet<_>>();
    for (fact, reference) in child {
        if seen.insert(pair_key(fact.to_string(), &reference)) {
            parent.push((fact, reference));
        }
    }
}

fn pair_key(fact_key: String, reference: &StoredForallConclusionReference) -> String {
    format!(
        "{}|{}|{:?}",
        fact_key, reference.source_fact_id, reference.conclusion_location
    )
}
