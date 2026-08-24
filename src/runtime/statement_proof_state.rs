//! Statement-local proof reuse and recursive inference guards.

use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

#[derive(Default)]
pub struct StatementProofScopeState {
    atomic_fact_proofs: HashMap<FactString, Rc<SuccessVerifyFactResult>>,
    well_defined_object_proofs: HashMap<WellDefinedCacheKey, Rc<SuccessVerifyObjWellDefinedResult>>,
    active_atomic_fact_inferences: HashSet<FactString>,
    active_well_defined_objects: HashSet<ObjString>,
    active_set_builder_membership_unfolds: HashSet<FactString>,
    active_set_builder_forall_transport: bool,
}

/// Runtime-owned stack for one statement's transient proof state.
///
/// The first scope corresponds to the persistent execution target. Every
/// temporary environment adds one child scope. Lookups walk from inner to
/// outer; popping a local environment drops its local memo entries exactly.
pub struct StatementProofStateStack {
    scopes: Vec<StatementProofScopeState>,
}

impl StatementProofStateStack {
    pub fn new() -> Self {
        Self {
            scopes: vec![StatementProofScopeState::default()],
        }
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(StatementProofScopeState::default());
    }

    pub fn pop_scope(&mut self) {
        assert!(
            self.scopes.len() > 1,
            "statement proof base scope must not be popped"
        );
        self.scopes.pop();
    }

    fn current_scope_mut(&mut self) -> &mut StatementProofScopeState {
        self.scopes
            .last_mut()
            .expect("statement proof base scope should exist")
    }

    fn scopes_from_inner(&self) -> impl Iterator<Item = &StatementProofScopeState> {
        self.scopes.iter().rev()
    }

    fn scopes_mut(&mut self) -> impl Iterator<Item = &mut StatementProofScopeState> {
        self.scopes.iter_mut()
    }

    pub fn clear_preserving_scope_depth(&mut self) {
        let scope_count = self.scopes.len().max(1);
        self.scopes = (0..scope_count)
            .map(|_| StatementProofScopeState::default())
            .collect();
    }
}

impl Runtime {
    pub fn begin_atomic_fact_inference(&mut self, key: &FactString) -> bool {
        if self
            .statement_proof_state
            .scopes_from_inner()
            .any(|scope| scope.active_atomic_fact_inferences.contains(key))
        {
            return false;
        }
        self.statement_proof_state
            .current_scope_mut()
            .active_atomic_fact_inferences
            .insert(key.clone());
        true
    }

    pub fn end_atomic_fact_inference(&mut self, key: &FactString) {
        for scope in self.statement_proof_state.scopes_mut() {
            scope.active_atomic_fact_inferences.remove(key);
        }
    }

    pub fn begin_well_defined_object(&mut self, key: &ObjString) -> bool {
        if self
            .statement_proof_state
            .scopes_from_inner()
            .any(|scope| scope.active_well_defined_objects.contains(key))
        {
            return false;
        }
        self.statement_proof_state
            .current_scope_mut()
            .active_well_defined_objects
            .insert(key.clone());
        true
    }

    pub fn end_well_defined_object(&mut self, key: &ObjString) {
        for scope in self.statement_proof_state.scopes_mut() {
            scope.active_well_defined_objects.remove(key);
        }
    }

    pub fn has_active_set_builder_membership_unfold(&self) -> bool {
        self.statement_proof_state
            .scopes_from_inner()
            .any(|scope| !scope.active_set_builder_membership_unfolds.is_empty())
    }

    pub fn begin_set_builder_membership_unfold(&mut self, key: &FactString) -> bool {
        if self
            .statement_proof_state
            .scopes_from_inner()
            .any(|scope| scope.active_set_builder_membership_unfolds.contains(key))
        {
            return false;
        }
        self.statement_proof_state
            .current_scope_mut()
            .active_set_builder_membership_unfolds
            .insert(key.clone());
        true
    }

    pub fn end_set_builder_membership_unfold(&mut self, key: &FactString) {
        for scope in self.statement_proof_state.scopes_mut() {
            scope.active_set_builder_membership_unfolds.remove(key);
        }
    }

    pub fn set_builder_forall_transport_is_active(&self) -> bool {
        self.statement_proof_state
            .scopes_from_inner()
            .any(|scope| scope.active_set_builder_forall_transport)
    }

    pub fn set_set_builder_forall_transport_active(&mut self, active: bool) {
        if active {
            self.statement_proof_state
                .current_scope_mut()
                .active_set_builder_forall_transport = true;
            return;
        }
        for scope in self.statement_proof_state.scopes_mut() {
            scope.active_set_builder_forall_transport = false;
        }
    }

    /// Reuse a completed proof visible in the current environment chain.
    pub fn verify_atomic_fact_from_statement_memo(&self, fact: &AtomicFact) -> Option<StmtResult> {
        let key = fact.to_string();
        self.statement_proof_state
            .scopes_from_inner()
            .find_map(|scope| {
                scope.atomic_fact_proofs.get(&key).map(|source| {
                    SuccessFactStmtResult::new_with_statement_memo(
                        fact.clone().into(),
                        SuccessInferResult::new(),
                        source.clone(),
                    )
                    .into()
                })
            })
    }

    /// Remember truth and its complete proof without committing the fact or running inference.
    pub fn remember_successful_atomic_fact_for_statement(
        &mut self,
        fact: &AtomicFact,
        mut result: StmtResult,
    ) -> StmtResult {
        if result.is_unknown() {
            return result;
        }

        if let Some(success) = result.factual_success_mut() {
            if let Some(verification) = Rc::get_mut(&mut success.verification) {
                self.attach_known_fact_ids_to_verified_by(verification.proof_mut())
                    .expect("successful proof FactId attachment should not fail");
            }
        }

        let key = fact.to_string();
        let existing_source = {
            self.statement_proof_state
                .scopes_from_inner()
                .find_map(|scope| scope.atomic_fact_proofs.get(&key).cloned())
        };
        if existing_source.is_some() {
            return result;
        }

        let source = result
            .factual_success()
            .expect("successful atomic fact verification must return a factual result");
        let source = source.verification.clone();
        self.statement_proof_state
            .current_scope_mut()
            .atomic_fact_proofs
            .insert(key, source.clone());

        result
    }

    /// End the statement-local lifetime on every active scope of the current execution frame.
    pub fn clear_statement_proof_state(&mut self) {
        self.statement_proof_state.clear_preserving_scope_depth();
    }

    pub fn statement_well_defined_object_proof(
        &self,
        key: &WellDefinedCacheKey,
    ) -> Option<Rc<SuccessVerifyObjWellDefinedResult>> {
        self.statement_proof_state
            .scopes_from_inner()
            .find_map(|scope| scope.well_defined_object_proofs.get(key).cloned())
    }

    pub fn remember_statement_well_defined_object_proof(
        &mut self,
        key: WellDefinedCacheKey,
        result: Rc<SuccessVerifyObjWellDefinedResult>,
    ) {
        self.statement_proof_state
            .current_scope_mut()
            .well_defined_object_proofs
            .entry(key)
            .or_insert(result);
    }
}

#[cfg(test)]
#[path = "../../tests/unit/runtime/statement_proof_state/tests.rs"]
mod tests;
