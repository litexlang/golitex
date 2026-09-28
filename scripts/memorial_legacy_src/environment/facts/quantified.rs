//! Environment-owned existential and disjunctive facts.

use crate::prelude::*;
use std::collections::{HashMap, HashSet};

/// Stored existential facts indexed by their structural key.
#[derive(Clone)]
pub struct ExistFactMemory {
    pub by_key: HashMap<ExistFactKey, Vec<ExistFact>>,
}

/// Stored disjunctive facts indexed by their structural key.
#[derive(Clone)]
pub struct OrFactMemory {
    pub by_key: HashMap<OrFactKey, Vec<OrFact>>,
}

impl ExistFactMemory {
    pub fn new() -> Self {
        Self {
            by_key: HashMap::new(),
        }
    }

    pub fn merge_from(&mut self, child: Self) {
        for (key, child_facts) in child.by_key {
            let parent_facts = self.by_key.entry(key).or_default();
            append_missing_exist_facts(parent_facts, child_facts);
        }
    }
}

impl OrFactMemory {
    pub fn new() -> Self {
        Self {
            by_key: HashMap::new(),
        }
    }

    pub fn merge_from(&mut self, child: Self) {
        for (key, child_facts) in child.by_key {
            let parent_facts = self.by_key.entry(key).or_default();
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
