//! Search index for conclusions projected from stored forall facts.
//!
//! Full forall text stays in `KnownFactMemory.facts_by_id`. Index entries are
//! `ForallConclusionCite` (fact id + `ForallConclusionLocation` path).

use crate::new_pipeline::ast::fact::{
    AndFactComponentForallConclusionLocation, AtomicFact, DirectForallConclusionLocation,
    ExistOrAndChainAtomicFact, ForallConclusionLocation, ForallFact,
};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::exec_env::helper::atomic_fact_has_positive_polarity;
use crate::new_pipeline::runtime::FactId;
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
}

impl KnownForallConclusionMemory {
    pub fn new() -> Self {
        Self::default()
    }

    // Project atomic leaves from each then (direct / and components).
    // Or/exist thens are not projected into atomic buckets.
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
                ExistOrAndChainAtomicFact::ChainFact(_)
                | ExistOrAndChainAtomicFact::OrFact(_)
                | ExistOrAndChainAtomicFact::ExistFact(_) => {}
            }
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
        ForallConclusionLocation::ChainFactComponent(_) => None,
    }
}
