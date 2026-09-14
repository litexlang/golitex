//! Environment-owned atomic-except-equality atomic facts and their search index.

use crate::prelude::*;
use std::collections::{HashMap, HashSet};

/// Atomic-except-equality atomic facts indexed by predicate family, polarity, and argument arity.
#[derive(Clone)]
pub struct AtomicExceptEqualityFactMemory {
    pub by_other_arg_count: HashMap<(AtomicFactKey, bool), Vec<AtomicFact>>,
    pub by_one_arg: HashMap<(AtomicFactKey, bool), HashMap<ObjString, AtomicFact>>,
    pub by_two_args: HashMap<(AtomicFactKey, bool), HashMap<(ObjString, ObjString), AtomicFact>>,
}

impl AtomicExceptEqualityFactMemory {
    pub fn new() -> Self {
        Self {
            by_other_arg_count: HashMap::new(),
            by_one_arg: HashMap::new(),
            by_two_args: HashMap::new(),
        }
    }

    pub fn merge_from(&mut self, child: Self) {
        for (key, child_facts) in child.by_other_arg_count {
            let parent_facts = self.by_other_arg_count.entry(key).or_default();
            append_missing_atomic_facts(parent_facts, child_facts);
        }
        for (key, child_facts) in child.by_one_arg {
            self.by_one_arg.entry(key).or_default().extend(child_facts);
        }
        for (key, child_facts) in child.by_two_args {
            self.by_two_args.entry(key).or_default().extend(child_facts);
        }
    }
}

fn append_missing_atomic_facts(parent: &mut Vec<AtomicFact>, child: Vec<AtomicFact>) {
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
