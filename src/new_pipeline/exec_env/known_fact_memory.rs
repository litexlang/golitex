use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, ExistFactFamily, Fact, OrFact};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::ast::obj::{AnonymousFn, FnSet, Obj, SetBuilder, FunctionSpace, SetFormer};
use crate::new_pipeline::exec_env::exist_fact_index_key::{exist_fact_index_key, ExistFactIndexKey};
use crate::new_pipeline::exec_env::known_forall_conclusion_memory::KnownForallConclusionMemory;
use crate::new_pipeline::runtime::FactId;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub use crate::new_pipeline::display_and_ir::ObjIR;

// Known facts and search indexes for one ExecEnv scope.
// Authority is facts_by_id plus known-* search indexes. Fact verify has no
// exact-IR cite slot. Rationale: `new_pipeline/identifier_identity.md`.
#[derive(Clone)]
pub struct KnownFactMemory {
    // Canonical store: every stored fact's full AST keyed by FactId.
    // Proof and exec results cite only ids; renderers resolve id → fact text
    // for per-statement JSON and later Lean compilation replay.
    pub facts_by_id: HashMap<FactId, Fact>,

    // Equality classes: generating EqualFacts as undirected edges, plus shared
    // member lists. Path search cites only FactIds from generating edges.
    // Example: store `a = b` and `b = c` → a,b,c share one class; path a→b→c uses those edges.
    pub known_equivalence_classes: KnownEquivalenceClassMemory,

    // Non-closed side → closed numeric representative + citing equality FactId.
    // Example: store `a = 10` → key `a` maps to `(10, fact_id)`.
    pub known_closed_numeric_equal: HashMap<ObjIR, Vec<(Obj, FactId)>>,

    // Non-literal side → binder-carrying obj (FnSet / AnonymousFn / SetBuilder) + FactId.
    // Example: `trust R_TO_R = fn(x R) R`, `have x fn(y R) R`, then `x $in R_TO_R`
    // via lookup on `R_TO_R` + alpha-equal FnSet (ByEqualToObjWithFreeParamsLookup).
    pub known_equal_to_obj_with_free_params: KnownEqualToObjWithFreeParamsMemory,

    // Non-equality atomics bucketed by (prop name, positive polarity).
    // Example: `a > 0` and `not a > 0` land in different buckets.
    pub known_atomic_except_equality_facts: AtomicExceptEqualityFactMemory,

    // Whole or-facts indexed by structural key (argument objs not part of the key).
    // Example: `a = 0 or a != 0` stored under the or-shape key for later cite/match.
    pub known_or: OrFactMemory,

    // Whole exist-facts indexed by structural key (binders / free objs not in the key).
    // Example: `exist x R st {x > 0}` stored for later exist-fact lookup.
    pub known_exist: ExistFactMemory,

    // Forall then-clauses projected for conclusion-shaped lookup.
    // Example: after storing
    //   forall x R:
    //       x > 0
    //       =>:
    //           x != 0
    // the then-clause shape is indexed so a goal `a != 0` can find matching foralls.
    pub known_forall_conclusions: KnownForallConclusionMemory,
}

/// Fact-index: `a = fn(…)` / `a = fn(…){…}` / `a = {x T: …}` with exactly one such side.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KnownEqualToObjWithFreeParamsShape {
    FnSet(FnSet),
    AnonymousFn(AnonymousFn),
    SetBuilder(SetBuilder),
}

#[derive(Clone, Default)]
pub struct KnownEqualToObjWithFreeParamsMemory {
    pub by_other_side: HashMap<ObjIR, Vec<(KnownEqualToObjWithFreeParamsShape, FactId)>>,
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
// Path search (EqualFactSearchedProofByEquivalenceClass) must cite only FactIds
// from generating_edges; the shared Rc is an index, not Lean-transformable proof.
#[derive(Clone, Default)]
pub struct KnownEquivalenceClassMemory {
    // Undirected adjacency of generating EqualFacts, keyed by obj IR.
    // Each store(a = b) inserts both a→b and b→a with the same EqualFact.
    pub generating_edges: HashMap<ObjIR, Vec<(ObjIR, EqualFact)>>,

    // Shared member list per equivalence class. Same class <=> Rc::ptr_eq.
    pub class_members: HashMap<ObjIR, Rc<Vec<Obj>>>,
}

// Non-equality atomics bucketed by (prop name, positive polarity).
// Lookup is a linear scan; arg sameness uses equality-class ObjIR, not a hash key.
#[derive(Clone, Default)]
pub struct AtomicExceptEqualityFactMemory {
    pub by_prop: HashMap<(AtomicName, bool), Vec<AtomicFact>>,
}

// Stored whole or-facts by structural index key (args not included).
#[derive(Clone, Default)]
pub struct OrFactMemory {
    pub by_key: HashMap<crate::new_pipeline::exec_env::or_fact_index_key::OrFactIndexKey, Vec<OrFact>>,
}

// Stored whole exist-facts by structural index key (binders/free objs not included).
#[derive(Clone, Default)]
pub struct ExistFactMemory {
    pub by_key: HashMap<ExistFactIndexKey, Vec<ExistFactFamily>>,
}

impl KnownFactMemory {
    pub fn new() -> Self {
        Self {
            facts_by_id: HashMap::new(),
            known_equivalence_classes: KnownEquivalenceClassMemory::new(),
            known_closed_numeric_equal: HashMap::new(),
            known_equal_to_obj_with_free_params: KnownEqualToObjWithFreeParamsMemory::new(),
            known_atomic_except_equality_facts: AtomicExceptEqualityFactMemory::new(),
            known_or: OrFactMemory::new(),
            known_exist: ExistFactMemory::new(),
            known_forall_conclusions: KnownForallConclusionMemory::new(),
        }
    }

    // Record any closed fact by FactId. Forall also projects atomic then-clauses
    // into known_forall_conclusions.
    pub fn record_fact(&mut self, fact_id: FactId, fact: Fact) {
        if let Fact::ForallFact(forall) = &fact {
            self.known_forall_conclusions.index_forall(forall);
        }
        self.facts_by_id.insert(fact_id, fact);
    }

    pub fn record_atomic_fact(&mut self, fact_id: FactId, fact: AtomicFact) {
        self.record_fact(fact_id, Fact::AtomicFact(fact));
    }
}

impl Default for KnownFactMemory {
    fn default() -> Self {
        Self::new()
    }
}

impl KnownEqualToObjWithFreeParamsMemory {
    pub fn new() -> Self {
        Self::default()
    }

    // When exactly one side is FnSet / AnonymousFn / SetBuilder, index the other.
    // Example: `trust R_TO_R = fn(x R) R` → key `R_TO_R` stores that FnSet + fact_id.
    pub fn maybe_index(&mut self, equal_fact: &EqualFact) {
        let left = free_params_shape_from_obj(&equal_fact.left);
        let right = free_params_shape_from_obj(&equal_fact.right);
        match (left, right) {
            (Some(shape), None) => {
                self.by_other_side
                    .entry(equal_fact.right.ir())
                    .or_default()
                    .push((shape, equal_fact.fact_id));
            }
            (None, Some(shape)) => {
                self.by_other_side
                    .entry(equal_fact.left.ir())
                    .or_default()
                    .push((shape, equal_fact.fact_id));
            }
            _ => {}
        }
    }
}

pub(crate) fn free_params_shape_from_obj(obj: &Obj) -> Option<KnownEqualToObjWithFreeParamsShape> {
    match obj {
        Obj::FunctionSpace(FunctionSpace::FnSet(fn_set)) => Some(KnownEqualToObjWithFreeParamsShape::FnSet(fn_set.clone())),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(anon)) => {
            Some(KnownEqualToObjWithFreeParamsShape::AnonymousFn(anon.clone()))
        }
        Obj::SetFormer(SetFormer::SetBuilder(set_builder)) => {
            Some(KnownEqualToObjWithFreeParamsShape::SetBuilder(set_builder.clone()))
        }
        _ => None,
    }
}

impl KnownEquivalenceClassMemory {
    pub fn new() -> Self {
        Self::default()
    }

    // Insert generating edge and merge class member lists.
    pub fn store(&mut self, equality: &EqualFact) {
        let left_key = equality.left.ir();
        let right_key = equality.right.ir();

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

    pub fn class_members_for(&self, key: &ObjIR) -> Option<&Rc<Vec<Obj>>> {
        self.class_members.get(key)
    }

    pub fn class_keys_for(&self, key: &ObjIR) -> Option<Vec<ObjIR>> {
        let members = self.class_members_for(key)?;
        Some(members.iter().map(|obj| obj.ir()).collect())
    }

    pub fn same_class(&self, left_key: &ObjIR, right_key: &ObjIR) -> bool {
        match (
            self.class_members.get(left_key),
            self.class_members.get(right_key),
        ) {
            (Some(left), Some(right)) => Rc::ptr_eq(left, right),
            _ => left_key == right_key,
        }
    }

    fn ensure_singleton(&mut self, key: &ObjIR, obj: &Obj) {
        if self.class_members.contains_key(key) {
            return;
        }
        self.class_members
            .insert(key.clone(), Rc::new(vec![obj.clone()]));
    }

    fn merge_classes(&mut self, left_key: &ObjIR, right_key: &ObjIR) {
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
            let key = obj.ir();
            if seen.insert(key) {
                merged.push(obj.clone());
            }
        }
        let new_rc = Rc::new(merged);
        for obj in new_rc.iter() {
            self.class_members.insert(obj.ir(), new_rc.clone());
        }
    }
}

impl AtomicExceptEqualityFactMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn store(&mut self, key: AtomicName, positive_polarity: bool, fact: AtomicFact) {
        self.by_prop
            .entry((key, positive_polarity))
            .or_default()
            .push(fact);
    }
}

impl OrFactMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn store(&mut self, or_fact: &OrFact) {
        let key = crate::new_pipeline::exec_env::or_fact_index_key::or_fact_index_key(or_fact);
        self.by_key.entry(key).or_default().push(or_fact.clone());
    }
}

impl ExistFactMemory {
    pub fn new() -> Self {
        Self::default()
    }

    // Example: store `exist x N st {x = 1}` under its ExistFactIndexKey bucket.
    pub fn store(&mut self, exist_fact: &ExistFactFamily) {
        let key = exist_fact_index_key(exist_fact);
        self.by_key.entry(key).or_default().push(exist_fact.clone());
    }
}

// When exactly one side classifies as ClosedNumericExpr, index the other.
// Both-closed or neither-closed: skip.
// Example: `a = 2^3/7 + 10 * 2.5` → key `a` stores closed RHS + fact_id.
pub fn maybe_index_known_closed_numeric_equal(
    index: &mut HashMap<ObjIR, Vec<(Obj, FactId)>>,
    equal_fact: &EqualFact,
) {
    use crate::new_pipeline::rational_expression::ClosedNumericExpr;

    let left = ClosedNumericExpr::try_from_obj(&equal_fact.left);
    let right = ClosedNumericExpr::try_from_obj(&equal_fact.right);
    match (left, right) {
        (Some(closed), None) => {
            index
                .entry(equal_fact.right.ir())
                .or_default()
                .push((closed.to_obj(), equal_fact.fact_id));
        }
        (None, Some(closed)) => {
            index
                .entry(equal_fact.left.ir())
                .or_default()
                .push((closed.to_obj(), equal_fact.fact_id));
        }
        _ => {}
    }
}
