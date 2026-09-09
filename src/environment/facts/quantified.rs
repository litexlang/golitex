//! Environment-owned existential and disjunctive facts.

use crate::prelude::*;
use std::collections::{HashMap, HashSet};

/// Stored existential and disjunctive facts indexed by their structural key.
#[derive(Clone)]
pub struct QuantifiedFactIndex {
    pub existential: HashMap<ExistFactKey, Vec<ExistFact>>,
    pub disjunctions: HashMap<OrFactKey, Vec<OrFact>>,
}

impl QuantifiedFactIndex {
    pub fn new() -> Self {
        Self {
            existential: HashMap::new(),
            disjunctions: HashMap::new(),
        }
    }

    pub fn merge_from(&mut self, child: Self) {
        for (key, child_facts) in child.existential {
            let parent_facts = self.existential.entry(key).or_default();
            append_missing_exist_facts(parent_facts, child_facts);
        }
        for (key, child_facts) in child.disjunctions {
            let parent_facts = self.disjunctions.entry(key).or_default();
            append_missing_or_facts(parent_facts, child_facts);
        }
    }
}

fn append_missing_exist_facts(parent: &mut Vec<ExistFact>, child: Vec<ExistFact>) {
    let mut seen = parent
        .iter()
        .map(ToString::to_string)
        .collect::<HashSet<_>>();
    for fact in child {
        if seen.insert(fact.to_string()) {
            parent.push(fact);
        }
    }
}

fn append_missing_or_facts(parent: &mut Vec<OrFact>, child: Vec<OrFact>) {
    let mut seen = parent
        .iter()
        .map(ToString::to_string)
        .collect::<HashSet<_>>();
    for fact in child {
        if seen.insert(fact.to_string()) {
            parent.push(fact);
        }
    }
}
