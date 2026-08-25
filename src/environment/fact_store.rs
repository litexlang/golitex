use crate::prelude::*;
use std::collections::HashMap;
use std::rc::Rc;

/// Canonical stored facts and the search indexes derived from them.
#[derive(Clone)]
pub struct EnvironmentFactStore {
    pub known_equality: KnownEquality,
    pub known_atomic_facts_with_0_or_more_than_2_args:
        HashMap<(AtomicFactKey, bool), Vec<AtomicFact>>,
    pub known_atomic_facts_with_1_arg:
        HashMap<(AtomicFactKey, bool), HashMap<ObjString, AtomicFact>>,
    pub known_atomic_facts_with_2_args:
        HashMap<(AtomicFactKey, bool), HashMap<(ObjString, ObjString), AtomicFact>>,
    pub known_owner_sets: HashMap<ObjString, HashMap<ObjString, InFact>>,
    pub known_direct_supersets: HashMap<ObjString, HashMap<ObjString, AtomicFact>>,
    pub known_exist_facts: HashMap<ExistFactKey, Vec<ExistFactEnum>>,
    pub known_or_facts: HashMap<OrFactKey, Vec<OrFact>>,
    pub known_atomic_facts_in_forall_facts:
        HashMap<(AtomicFactKey, bool), Vec<(AtomicFact, Rc<StoredForallConclusionReference>)>>,
    pub known_atomic_facts_in_forall_facts_by_arg_shape: AtomicFactInForallArgShapeIndex,
    pub known_exist_facts_in_forall_facts:
        HashMap<ExistFactKey, Vec<(ExistFactEnum, Rc<StoredForallConclusionReference>)>>,
    pub known_and_facts_in_forall_facts:
        HashMap<AndFactKey, Vec<(AndFact, Rc<StoredForallConclusionReference>)>>,
    pub known_or_facts_in_forall_facts:
        HashMap<OrFactKey, Vec<(OrFact, Rc<StoredForallConclusionReference>)>>,
    pub stored_facts: EnvironmentStoredFactStore,
}

impl EnvironmentFactStore {
    pub fn new() -> Self {
        Self {
            known_equality: KnownEquality::new(),
            known_atomic_facts_with_0_or_more_than_2_args: HashMap::new(),
            known_atomic_facts_with_1_arg: HashMap::new(),
            known_atomic_facts_with_2_args: HashMap::new(),
            known_owner_sets: HashMap::new(),
            known_direct_supersets: HashMap::new(),
            known_exist_facts: HashMap::new(),
            known_or_facts: HashMap::new(),
            known_atomic_facts_in_forall_facts: HashMap::new(),
            known_atomic_facts_in_forall_facts_by_arg_shape: HashMap::new(),
            known_exist_facts_in_forall_facts: HashMap::new(),
            known_and_facts_in_forall_facts: HashMap::new(),
            known_or_facts_in_forall_facts: HashMap::new(),
            stored_facts: EnvironmentStoredFactStore::default(),
        }
    }
}
