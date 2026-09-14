use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::new_pipeline::runtime::FactId;
use std::collections::HashMap;

pub type ObjKey = String;
pub type AtomicFactKey = String;

// Facts and search indexes for one ExecEnv scope (new_pipeline AST).
#[derive(Clone)]
pub struct KnownFactMemory {
    pub facts_by_id: HashMap<FactId, Fact>,
    pub known_equality: KnownEqualityMemory,
    pub known_atomic_except_equality_facts: AtomicExceptEqualityFactMemory,
}

// Direct equality edges keyed by `ast_obj_key`. Full union-find comes later.
#[derive(Clone, Default)]
pub struct KnownEqualityMemory {
    pub edges: HashMap<ObjKey, Vec<(ObjKey, EqualFact)>>,
}

// Non-equality atomics indexed by predicate key, polarity, and arity.
#[derive(Clone, Default)]
pub struct AtomicExceptEqualityFactMemory {
    pub by_other_arg_count: HashMap<(AtomicFactKey, bool), Vec<AtomicFact>>,
    pub by_one_arg: HashMap<(AtomicFactKey, bool), HashMap<ObjKey, AtomicFact>>,
    pub by_two_args: HashMap<(AtomicFactKey, bool), HashMap<(ObjKey, ObjKey), AtomicFact>>,
}

impl KnownFactMemory {
    pub fn new() -> Self {
        Self {
            facts_by_id: HashMap::new(),
            known_equality: KnownEqualityMemory::new(),
            known_atomic_except_equality_facts: AtomicExceptEqualityFactMemory::new(),
        }
    }
}

impl Default for KnownFactMemory {
    fn default() -> Self {
        Self::new()
    }
}

impl KnownEqualityMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn store(&mut self, equality: &EqualFact, left_key: ObjKey, right_key: ObjKey) {
        self.edges
            .entry(left_key.clone())
            .or_default()
            .push((right_key.clone(), equality.clone()));
        self.edges
            .entry(right_key)
            .or_default()
            .push((left_key, equality.clone()));
    }
}

impl AtomicExceptEqualityFactMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn store_one_arg(
        &mut self,
        key: AtomicFactKey,
        positive_polarity: bool,
        arg_key: ObjKey,
        fact: AtomicFact,
    ) {
        self.by_one_arg
            .entry((key, positive_polarity))
            .or_default()
            .insert(arg_key, fact);
    }

    pub fn store_two_args(
        &mut self,
        key: AtomicFactKey,
        positive_polarity: bool,
        arg_key0: ObjKey,
        arg_key1: ObjKey,
        fact: AtomicFact,
    ) {
        self.by_two_args
            .entry((key, positive_polarity))
            .or_default()
            .insert((arg_key0, arg_key1), fact);
    }

    pub fn store_other_arg_count(
        &mut self,
        key: AtomicFactKey,
        positive_polarity: bool,
        fact: AtomicFact,
    ) {
        self.by_other_arg_count
            .entry((key, positive_polarity))
            .or_default()
            .push(fact);
    }
}
