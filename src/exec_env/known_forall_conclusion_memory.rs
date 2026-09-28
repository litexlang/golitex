//! Search index for conclusions projected from stored forall facts.
//!
//! Full forall text stays in `KnownFactMemory.facts_by_id`. Index entries are
//! `ForallConclusionCite` (fact id + `ForallConclusionLocation` path).

use crate::ast::fact::{
    AndFactComponentForallConclusionLocation, AtomicFact, DirectForallConclusionLocation,
    ExistShapedFact, ExistOrAndChainAtomicFact, ForallConclusionLocation, ForallFact, OrFact,
};
use crate::ast::names::AtomicName;
use crate::ast::fact::atomic_fact_has_positive_polarity;
use crate::exec_env::exist_shaped_fact_index_key::{exist_shaped_fact_index_key, ExistShapedFactIndexKey};
use crate::exec_env::or_fact_index_key::{or_fact_index_key, OrFactIndexKey};
use crate::exec_env::forall_conclusion_index_key::{
    and_forall_conclusion_index_key, chain_forall_conclusion_index_key,
    AndForallConclusionIndexKey, ChainForallConclusionIndexKey,
};
use crate::runtime::FactId;
use std::collections::HashMap;

/// Cite a stored forall conclusion: which fact + where inside its then-tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForallConclusionCite {
    pub fact_id: FactId,
    pub location: ForallConclusionLocation,
}

#[derive(Clone, Default)]
pub struct KnownForallConclusionMemory {
    /// Non-equality atomic leaves (`≠` included here).
    pub by_atomic_prop: HashMap<(AtomicName, bool), Vec<ForallConclusionCite>>,
    /// Only `=` leaves (not `≠`).
    pub equal_conclusions: Vec<ForallConclusionCite>,
    /// Whole or then-clauses, keyed by structural or index key.
    pub by_or: HashMap<OrFactIndexKey, Vec<ForallConclusionCite>>,
    /// Whole exist then-clauses, keyed by structural exist index key.
    pub by_exist: HashMap<ExistShapedFactIndexKey, Vec<ForallConclusionCite>>,
    /// Whole and then-clauses, keyed by component shape. This is what lets
    /// `and/components.lit` match a forall conclusion before proving its
    /// components.
    pub by_and: HashMap<AndForallConclusionIndexKey, Vec<ForallConclusionCite>>,
    /// Whole chain then-clauses, keyed by ordered operator shape. This is what
    /// lets `chain/adjacent_order.lit` instantiate `x < y < z` as a whole.
    pub by_chain: HashMap<ChainForallConclusionIndexKey, Vec<ForallConclusionCite>>,
}

impl KnownForallConclusionMemory {
    pub fn new() -> Self {
        Self::default()
    }

    // Project atomic leaves, whole or thens, and whole exist thens.
    // Chain thens are not projected into these buckets yet.
    pub fn index_forall(&mut self, forall: &ForallFact) {
        let fact_id = forall.fact_id;
        for (then_fact_index, then) in forall.then_facts.iter().enumerate() {
            match then {
                ExistOrAndChainAtomicFact::AtomicFact(atomic) => {
                    self.push_atomic_leaf(
                        atomic,
                        ForallConclusionCite {
                            fact_id,
                            location: ForallConclusionLocation::DirectThenFact(
                                DirectForallConclusionLocation { then_fact_index },
                            ),
                        },
                    );
                }
                ExistOrAndChainAtomicFact::AndFact(and_fact) => {
                    self.by_and
                        .entry(and_forall_conclusion_index_key(and_fact))
                        .or_default()
                        .push(ForallConclusionCite {
                            fact_id,
                            location: ForallConclusionLocation::DirectThenFact(
                                DirectForallConclusionLocation { then_fact_index },
                            ),
                        });
                    for (component_index, atomic) in and_fact.facts.iter().enumerate() {
                        self.push_atomic_leaf(
                            atomic,
                            ForallConclusionCite {
                                fact_id,
                                location: ForallConclusionLocation::AndFactComponent(
                                    AndFactComponentForallConclusionLocation {
                                        then_fact_index,
                                        component_index,
                                    },
                                ),
                            },
                        );
                    }
                }
                ExistOrAndChainAtomicFact::OrFact(or_fact) => {
                    let key = or_fact_index_key(or_fact);
                    self.by_or.entry(key).or_default().push(ForallConclusionCite {
                        fact_id,
                        location: ForallConclusionLocation::DirectThenFact(
                            DirectForallConclusionLocation { then_fact_index },
                        ),
                    });
                }
                ExistOrAndChainAtomicFact::ExistFact(plain) => {
                    let key = exist_shaped_fact_index_key(&ExistShapedFact::Exist(plain.clone()));
                    self.by_exist
                        .entry(key)
                        .or_default()
                        .push(ForallConclusionCite {
                            fact_id,
                            location: ForallConclusionLocation::DirectThenFact(
                                DirectForallConclusionLocation { then_fact_index },
                            ),
                        });
                }
                ExistOrAndChainAtomicFact::ExistUniqueFact(plain) => {
                    let key = exist_shaped_fact_index_key(&ExistShapedFact::ExistUnique(plain.clone()));
                    self.by_exist
                        .entry(key)
                        .or_default()
                        .push(ForallConclusionCite {
                            fact_id,
                            location: ForallConclusionLocation::DirectThenFact(
                                DirectForallConclusionLocation { then_fact_index },
                            ),
                        });
                }
                ExistOrAndChainAtomicFact::NotExistFact(plain) => {
                    let key = exist_shaped_fact_index_key(&ExistShapedFact::NotExist(plain.clone()));
                    self.by_exist
                        .entry(key)
                        .or_default()
                        .push(ForallConclusionCite {
                            fact_id,
                            location: ForallConclusionLocation::DirectThenFact(
                                DirectForallConclusionLocation { then_fact_index },
                            ),
                        });
                }
                ExistOrAndChainAtomicFact::ChainFact(chain) => {
                    self.by_chain
                        .entry(chain_forall_conclusion_index_key(chain))
                        .or_default()
                        .push(ForallConclusionCite {
                            fact_id,
                            location: ForallConclusionLocation::DirectThenFact(
                                DirectForallConclusionLocation { then_fact_index },
                            ),
                        });
                }
            }
        }
    }

    /// Project the already elaborated adjacent atoms of a chain conclusion.
    /// Chain atoms are built by Runtime so builtin operators keep their exact
    /// AtomicFact variant; this memory only records their source location.
    pub fn index_chain_components(
        &mut self,
        forall: &ForallFact,
        then_fact_index: usize,
        adjacent: &[AtomicFact],
    ) {
        let fact_id = forall.fact_id;
        for (component_index, atomic) in adjacent.iter().enumerate() {
            self.push_atomic_leaf(
                atomic,
                ForallConclusionCite {
                    fact_id,
                    location: ForallConclusionLocation::ChainFactComponent(
                        crate::ast::fact::ChainFactComponentForallConclusionLocation {
                            then_fact_index,
                            component_index,
                        },
                    ),
                },
            );
        }
    }

    pub fn merge_from(&mut self, child: &KnownForallConclusionMemory) {
        for entry in &child.equal_conclusions {
            if !self.equal_conclusions.iter().any(|e| e == entry) {
                self.equal_conclusions.push(entry.clone());
            }
        }
        for (key, child_entries) in &child.by_atomic_prop {
            let parent_entries = self.by_atomic_prop.entry(key.clone()).or_default();
            for entry in child_entries {
                if !parent_entries.iter().any(|e| e == entry) {
                    parent_entries.push(entry.clone());
                }
            }
        }
        for (key, child_entries) in &child.by_or {
            let parent_entries = self.by_or.entry(key.clone()).or_default();
            for entry in child_entries {
                if !parent_entries.iter().any(|e| e == entry) {
                    parent_entries.push(entry.clone());
                }
            }
        }
        for (key, child_entries) in &child.by_exist {
            let parent_entries = self.by_exist.entry(key.clone()).or_default();
            for entry in child_entries {
                if !parent_entries.iter().any(|e| e == entry) {
                    parent_entries.push(entry.clone());
                }
            }
        }
        for (key, child_entries) in &child.by_and {
            let parent_entries = self.by_and.entry(key.clone()).or_default();
            for entry in child_entries {
                if !parent_entries.iter().any(|e| e == entry) {
                    parent_entries.push(entry.clone());
                }
            }
        }
        for (key, child_entries) in &child.by_chain {
            let parent_entries = self.by_chain.entry(key.clone()).or_default();
            for entry in child_entries {
                if !parent_entries.iter().any(|e| e == entry) {
                    parent_entries.push(entry.clone());
                }
            }
        }
    }

    fn push_atomic_leaf(&mut self, atomic: &AtomicFact, cite: ForallConclusionCite) {
        match atomic {
            AtomicFact::EqualFact(_) => self.equal_conclusions.push(cite),
            _ => {
                let key = (atomic.prop_name(), atomic_fact_has_positive_polarity(atomic));
                self.by_atomic_prop.entry(key).or_default().push(cite);
            }
        }
    }
}

/// Resolve the atomic leaf at `location` inside a stored forall.
pub fn atomic_at_forall_location(
    forall: &ForallFact,
    location: &ForallConclusionLocation,
) -> Option<AtomicFact> {
    match location {
        ForallConclusionLocation::DirectThenFact(loc) => {
            match forall.then_facts.get(loc.then_fact_index)? {
                ExistOrAndChainAtomicFact::AtomicFact(atomic) => Some(atomic.clone()),
                _ => None,
            }
        }
        ForallConclusionLocation::AndFactComponent(loc) => {
            let ExistOrAndChainAtomicFact::AndFact(and_fact) =
                forall.then_facts.get(loc.then_fact_index)?
            else {
                return None;
            };
            and_fact.facts.get(loc.component_index).cloned()
        }
        ForallConclusionLocation::ChainFactComponent(loc) => {
            let ExistOrAndChainAtomicFact::ChainFact(chain) =
                forall.then_facts.get(loc.then_fact_index)?
            else {
                return None;
            };
            let left = chain.objs.get(loc.component_index)?.clone();
            let right = chain.objs.get(loc.component_index + 1)?.clone();
            let prop = chain.prop_names.get(loc.component_index)?.clone();
            // Chain components are indexed with their elaborated AtomicFact;
            // this resolver is only used for direct evidence reconstruction.
            // The verifier replaces the cite with the indexed atom when it
            // needs the builtin-specific variant.
            let _ = (left, right, prop);
            None
        }
    }
}

/// Resolve a whole or then at `location` inside a stored forall.
pub fn or_at_forall_location(
    forall: &ForallFact,
    location: &ForallConclusionLocation,
) -> Option<OrFact> {
    match location {
        ForallConclusionLocation::DirectThenFact(loc) => {
            match forall.then_facts.get(loc.then_fact_index)? {
                ExistOrAndChainAtomicFact::OrFact(or_fact) => Some(or_fact.clone()),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Resolve a whole exist then at `location` inside a stored forall.
pub fn exist_at_forall_location(
    forall: &ForallFact,
    location: &ForallConclusionLocation,
) -> Option<ExistShapedFact> {
    match location {
        ForallConclusionLocation::DirectThenFact(loc) => {
            match forall.then_facts.get(loc.then_fact_index)? {
                ExistOrAndChainAtomicFact::ExistFact(plain) => {
                    Some(ExistShapedFact::Exist(plain.clone()))
                }
                ExistOrAndChainAtomicFact::ExistUniqueFact(plain) => {
                    Some(ExistShapedFact::ExistUnique(plain.clone()))
                }
                ExistOrAndChainAtomicFact::NotExistFact(plain) => {
                    Some(ExistShapedFact::NotExist(plain.clone()))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

pub fn and_at_forall_location(
    forall: &ForallFact,
    location: &ForallConclusionLocation,
) -> Option<crate::ast::fact::AndFact> {
    let ForallConclusionLocation::DirectThenFact(loc) = location else { return None; };
    match forall.then_facts.get(loc.then_fact_index)? {
        ExistOrAndChainAtomicFact::AndFact(and_fact) => Some(and_fact.clone()),
        _ => None,
    }
}

pub fn chain_at_forall_location(
    forall: &ForallFact,
    location: &ForallConclusionLocation,
) -> Option<crate::ast::fact::ChainFact> {
    let ForallConclusionLocation::DirectThenFact(loc) = location else { return None; };
    match forall.then_facts.get(loc.then_fact_index)? {
        ExistOrAndChainAtomicFact::ChainFact(chain) => Some(chain.clone()),
        _ => None,
    }
}
