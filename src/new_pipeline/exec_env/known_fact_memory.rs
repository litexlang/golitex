use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::new_pipeline::ast::obj::Obj;
use crate::new_pipeline::runtime::FactId;
use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub type ObjKey = String;

// Facts and search indexes for one ExecEnv scope (new_pipeline AST).
#[derive(Clone)]
pub struct KnownFactMemory {
    pub facts_by_id: HashMap<FactId, Fact>,
    pub known_equality: KnownEqualityMemory,
    pub known_atomic_except_equality_facts: AtomicExceptEqualityFactMemory,
}

// Equality equivalence-class store for one ExecEnv.
//
// Two views of the same data:
// 1. Class view: `class_members` — each key points at a shared `Rc<Vec<Obj>>` of
//    everyone currently in its equivalence class. After a merge (e.g. a=b and
//    c=d then b=c), all keys in the merged class share one Rc.
// 2. Evidence view: `generating_edges` — EqualFacts actually written into the
//    env (user or infer). Not the closed set of all equal pairs.
//
// Path search (EqualFactSearchedProofByKnownEquality) must cite only FactIds
// from generating_edges; the shared Rc is an index, not Lean-replayable proof.
#[derive(Clone, Default)]
pub struct KnownEqualityMemory {
    // Undirected adjacency of generating EqualFacts, keyed by obj internal representation.
    // Each store(a = b) inserts both a→b and b→a with the same EqualFact.
    pub generating_edges: HashMap<ObjKey, Vec<(ObjKey, EqualFact)>>,

    // Shared member list per equivalence class. Same class <=> Rc::ptr_eq.
    pub class_members: HashMap<ObjKey, Rc<Vec<Obj>>>,
}

// Non-equality atomics indexed by prop_name, polarity, and arity.
#[derive(Clone, Default)]
pub struct AtomicExceptEqualityFactMemory {
    pub by_other_arg_count: HashMap<(PropName, bool), Vec<AtomicFact>>,
    pub by_one_arg: HashMap<(PropName, bool), HashMap<ObjKey, AtomicFact>>,
    pub by_two_args: HashMap<(PropName, bool), HashMap<(ObjKey, ObjKey), AtomicFact>>,
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

    // Insert generating edge and merge class member lists.
    pub fn store(&mut self, equality: &EqualFact) {
        let left_key = equality.left.internal_representation();
        let right_key = equality.right.internal_representation();

        self.generating_edges
            .entry(left_key.clone())
            .or_default()
            .push((right_key.clone(), equality.clone()));
        self.generating_edges
            .entry(right_key.clone())
            .or_default()
            .push((left_key.clone(), equality.clone()));

        self.ensure_singleton(&left_key, &equality.left);
        self.ensure_singleton(&right_key, &equality.right);
        self.merge_classes(&left_key, &right_key);
    }

    pub fn class_members_for(&self, key: &str) -> Option<&Rc<Vec<Obj>>> {
        self.class_members.get(key)
    }

    pub fn class_keys_for(&self, key: &str) -> Option<Vec<ObjKey>> {
        let members = self.class_members_for(key)?;
        Some(
            members
                .iter()
                .map(|obj| obj.internal_representation())
                .collect(),
        )
    }

    pub fn same_class(&self, left_key: &str, right_key: &str) -> bool {
        match (
            self.class_members.get(left_key),
            self.class_members.get(right_key),
        ) {
            (Some(left), Some(right)) => Rc::ptr_eq(left, right),
            _ => left_key == right_key,
        }
    }

    fn ensure_singleton(&mut self, key: &ObjKey, obj: &Obj) {
        if self.class_members.contains_key(key) {
            return;
        }
        self.class_members
            .insert(key.clone(), Rc::new(vec![obj.clone()]));
    }

    fn merge_classes(&mut self, left_key: &ObjKey, right_key: &ObjKey) {
        let left_rc = self
            .class_members
            .get(left_key)
            .expect("left class missing after ensure_singleton")
            .clone();
        let right_rc = self
            .class_members
            .get(right_key)
            .expect("right class missing after ensure_singleton")
            .clone();
        if Rc::ptr_eq(&left_rc, &right_rc) {
            return;
        }

        let mut merged = Vec::new();
        let mut seen = HashSet::new();
        for obj in left_rc.iter().chain(right_rc.iter()) {
            let key = obj.internal_representation();
            if seen.insert(key) {
                merged.push(obj.clone());
            }
        }
        let new_rc = Rc::new(merged);
        for obj in new_rc.iter() {
            self.class_members
                .insert(obj.internal_representation(), new_rc.clone());
        }
    }
}

impl AtomicExceptEqualityFactMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn store_one_arg(
        &mut self,
        key: PropName,
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
        key: PropName,
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
        key: PropName,
        positive_polarity: bool,
        fact: AtomicFact,
    ) {
        self.by_other_arg_count
            .entry((key, positive_polarity))
            .or_default()
            .push(fact);
    }
}
