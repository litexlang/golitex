//! Transient memoization and recursion guards for one proof-search tree.

use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Debug, Default)]
struct ProofSearchScopeState {
    parent: Option<usize>,
    atomic_fact_proofs: HashMap<FactString, Rc<SuccessFactProofNode>>,
    well_defined_object_proofs: HashMap<ObjString, Rc<SuccessVerifyDirectObjWellDefinedResult>>,
    active_well_defined_objects: HashSet<ObjString>,
    active_set_builder_membership_unfolds: HashSet<FactString>,
    active_set_builder_forall_transport: bool,
}

#[derive(Debug)]
pub(super) struct ProofSearchState {
    scopes: Vec<ProofSearchScopeState>,
}

impl ProofSearchState {
    pub(super) fn new() -> Self {
        Self {
            scopes: vec![ProofSearchScopeState::default()],
        }
    }

    pub(super) fn push_child_scope(&mut self, parent: usize) -> usize {
        let scope = self.scopes.len();
        self.scopes.push(ProofSearchScopeState {
            parent: Some(parent),
            ..ProofSearchScopeState::default()
        });
        scope
    }

    pub(super) fn begin_well_defined_object(&mut self, scope: usize, key: &ObjString) -> bool {
        if self.scope_chain_contains(scope, |state| {
            state.active_well_defined_objects.contains(key)
        }) {
            return false;
        }
        self.scopes[scope]
            .active_well_defined_objects
            .insert(key.clone());
        true
    }

    pub(super) fn well_defined_object_proof(
        &self,
        scope: usize,
        key: &ObjString,
    ) -> Option<Rc<SuccessVerifyDirectObjWellDefinedResult>> {
        self.find_in_scope_chain(scope, |state| {
            state.well_defined_object_proofs.get(key).cloned()
        })
    }

    pub(super) fn remember_well_defined_object_proof(
        &mut self,
        scope: usize,
        key: ObjString,
        result: Rc<SuccessVerifyDirectObjWellDefinedResult>,
    ) {
        if self.well_defined_object_proof(scope, &key).is_none() {
            self.scopes[scope]
                .well_defined_object_proofs
                .insert(key, result);
        }
    }

    pub(super) fn end_well_defined_object(&mut self, scope: usize, key: &ObjString) {
        self.scopes[scope].active_well_defined_objects.remove(key);
    }

    pub(super) fn has_active_set_builder_membership_unfold(&self, scope: usize) -> bool {
        self.scope_chain_contains(scope, |state| {
            !state.active_set_builder_membership_unfolds.is_empty()
        })
    }

    pub(super) fn begin_set_builder_membership_unfold(
        &mut self,
        scope: usize,
        key: &FactString,
    ) -> bool {
        if self.scope_chain_contains(scope, |state| {
            state.active_set_builder_membership_unfolds.contains(key)
        }) {
            return false;
        }
        self.scopes[scope]
            .active_set_builder_membership_unfolds
            .insert(key.clone());
        true
    }

    pub(super) fn end_set_builder_membership_unfold(&mut self, scope: usize, key: &FactString) {
        self.scopes[scope]
            .active_set_builder_membership_unfolds
            .remove(key);
    }

    pub(super) fn set_builder_forall_transport_is_active(&self, scope: usize) -> bool {
        self.scope_chain_contains(scope, |state| state.active_set_builder_forall_transport)
    }

    pub(super) fn set_set_builder_forall_transport_active(&mut self, scope: usize, active: bool) {
        if active {
            self.scopes[scope].active_set_builder_forall_transport = true;
            return;
        }
        self.scopes[scope].active_set_builder_forall_transport = false;
    }

    pub(super) fn atomic_fact_proof(
        &self,
        scope: usize,
        key: &FactString,
    ) -> Option<Rc<SuccessFactProofNode>> {
        self.find_in_scope_chain(scope, |state| state.atomic_fact_proofs.get(key).cloned())
    }

    pub(super) fn remember_atomic_fact_proof(
        &mut self,
        scope: usize,
        key: FactString,
        result: Rc<SuccessFactProofNode>,
    ) {
        if self.atomic_fact_proof(scope, &key).is_none() {
            self.scopes[scope].atomic_fact_proofs.insert(key, result);
        }
    }

    fn scope_chain_contains(
        &self,
        scope: usize,
        predicate: impl Fn(&ProofSearchScopeState) -> bool,
    ) -> bool {
        let mut current = Some(scope);
        while let Some(index) = current {
            let state = &self.scopes[index];
            if predicate(state) {
                return true;
            }
            current = state.parent;
        }
        false
    }

    fn find_in_scope_chain<T>(
        &self,
        scope: usize,
        find: impl Fn(&ProofSearchScopeState) -> Option<T>,
    ) -> Option<T> {
        let mut current = Some(scope);
        while let Some(index) = current {
            let state = &self.scopes[index];
            if let Some(value) = find(state) {
                return Some(value);
            }
            current = state.parent;
        }
        None
    }
}
