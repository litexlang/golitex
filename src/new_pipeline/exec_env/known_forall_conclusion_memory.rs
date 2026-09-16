//! Search index for atomic then-clauses of stored forall facts.
//!
//! Full forall text stays in `KnownFactMemory.facts_by_id`. Entries cite by
//! `source_fact_id` + `then_fact_index` only (Lean-friendly).

use crate::new_pipeline::ast::fact::{AtomicFact, ExistOrAndChainAtomicFact, ForallFact};
use crate::new_pipeline::ast::names::AtomicName;
use crate::new_pipeline::exec_env::helper::atomic_fact_has_positive_polarity;
use crate::new_pipeline::runtime::FactId;
use std::collections::HashMap;

#[derive(Clone, Default)]
pub struct KnownForallConclusionMemory {
    /// Non-equality atomic then (`≠` included here).
    pub by_atomic_prop: HashMap<(AtomicName, bool), Vec<IndexedForallAtomicConclusion>>,
    /// Only `=` then-atoms (not `≠`).
    pub equal_conclusions: Vec<IndexedForallAtomicConclusion>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexedForallAtomicConclusion {
    pub source_fact_id: FactId,
    pub then_fact_index: usize,
}

impl KnownForallConclusionMemory {
    pub fn new() -> Self {
        Self::default()
    }

    // Index every direct atomic then of a stored forall (phase 1).
    pub fn index_forall(&mut self, forall: &ForallFact) {
        let source_fact_id = forall.fact_id;
        for (then_fact_index, then) in forall.then_facts.iter().enumerate() {
            let ExistOrAndChainAtomicFact::AtomicFact(atomic) = then else {
                continue;
            };
            let entry = IndexedForallAtomicConclusion {
                source_fact_id,
                then_fact_index,
            };
            match atomic {
                AtomicFact::EqualFact(_) => self.equal_conclusions.push(entry),
                _ => {
                    let key = (atomic.prop_name(), atomic_fact_has_positive_polarity(atomic));
                    self.by_atomic_prop.entry(key).or_default().push(entry);
                }
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
}
