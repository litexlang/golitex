//! Transient recursion state for one explicit inference call tree.

use crate::prelude::{nested_obj_binder_normalized_fact_key, AtomicFact, FactString};
use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

#[derive(Clone, Debug, Default)]
pub struct InferenceState {
    active_atomic_facts: Rc<RefCell<HashSet<FactString>>>,
}

impl InferenceState {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn enter_atomic_fact(&self, atomic_fact: &AtomicFact) -> Option<ActiveAtomicInference> {
        let key = nested_obj_binder_normalized_fact_key(&atomic_fact.clone().into());
        if !self.active_atomic_facts.borrow_mut().insert(key.clone()) {
            return None;
        }
        Some(ActiveAtomicInference {
            state: self.clone(),
            key,
        })
    }
}

pub struct ActiveAtomicInference {
    state: InferenceState,
    key: FactString,
}

impl Drop for ActiveAtomicInference {
    fn drop(&mut self) {
        self.state
            .active_atomic_facts
            .borrow_mut()
            .remove(&self.key);
    }
}

#[cfg(test)]
#[path = "../../tests/unit/inference/state.rs"]
mod tests;
