//! Verification options threaded through recursive proof search.

use super::state::ProofSearchState;
use crate::prelude::*;
use std::cell::RefCell;
use std::rc::Rc;

/// Control flags for one recursive verification attempt.
///
/// `proof_search_round` bounds how aggressively recursive verification may retry a goal.
/// Round 0 is the normal path. Later rounds are used by callers that need a
/// more restricted retry to avoid repeatedly re-entering the same known-forall,
/// strategy, or well-definedness search. Round 2 is the final retry.
///
#[derive(Clone, Debug)]
pub struct VerifyState {
    pub proof_search_round: u8,
    proof_search: Rc<RefCell<ProofSearchState>>,
    proof_scope: usize,
    inference: InferenceState,
}

impl VerifyState {
    const FINAL_ROUND: u8 = 2;

    pub fn initial() -> Self {
        Self::standard(0)
    }

    pub fn final_round() -> Self {
        Self::standard(Self::FINAL_ROUND)
    }

    fn standard(proof_search_round: u8) -> Self {
        Self {
            proof_search_round,
            proof_search: Rc::new(RefCell::new(ProofSearchState::new())),
            proof_scope: 0,
            inference: InferenceState::new(),
        }
    }

    pub fn with_next_round(&self) -> Self {
        Self {
            proof_search_round: self.proof_search_round + 1,
            ..self.clone()
        }
    }

    pub fn with_final_round(&self) -> Self {
        Self {
            proof_search_round: Self::FINAL_ROUND,
            ..self.clone()
        }
    }

    pub fn with_child_proof_scope(&self) -> Self {
        let proof_scope = self
            .proof_search
            .borrow_mut()
            .push_child_scope(self.proof_scope);
        Self {
            proof_scope,
            ..self.clone()
        }
    }

    pub fn with_inference_state(&self, inference: &InferenceState) -> Self {
        Self {
            inference: inference.clone(),
            ..self.clone()
        }
    }

    pub fn inference_state(&self) -> &InferenceState {
        &self.inference
    }

    pub fn is_initial_round(&self) -> bool {
        self.proof_search_round == 0
    }

    pub(in crate::verification) fn begin_well_defined_object(&self, key: &ObjString) -> bool {
        self.proof_search
            .borrow_mut()
            .begin_well_defined_object(self.proof_scope, key)
    }

    pub(in crate::verification) fn end_well_defined_object(&self, key: &ObjString) {
        self.proof_search
            .borrow_mut()
            .end_well_defined_object(self.proof_scope, key);
    }

    pub(in crate::verification) fn well_defined_object_proof(
        &self,
        key: &ObjString,
    ) -> Option<Rc<SuccessVerifyDirectObjWellDefinedResult>> {
        self.proof_search
            .borrow()
            .well_defined_object_proof(self.proof_scope, key)
    }

    pub(in crate::verification) fn remember_well_defined_object_proof(
        &self,
        key: ObjString,
        result: Rc<SuccessVerifyDirectObjWellDefinedResult>,
    ) {
        self.proof_search
            .borrow_mut()
            .remember_well_defined_object_proof(self.proof_scope, key, result);
    }

    pub(in crate::verification) fn has_active_set_builder_membership_unfold(&self) -> bool {
        self.proof_search
            .borrow()
            .has_active_set_builder_membership_unfold(self.proof_scope)
    }

    pub(in crate::verification) fn begin_set_builder_membership_unfold(
        &self,
        key: &FactString,
    ) -> bool {
        self.proof_search
            .borrow_mut()
            .begin_set_builder_membership_unfold(self.proof_scope, key)
    }

    pub(in crate::verification) fn end_set_builder_membership_unfold(&self, key: &FactString) {
        self.proof_search
            .borrow_mut()
            .end_set_builder_membership_unfold(self.proof_scope, key);
    }

    pub(in crate::verification) fn set_builder_forall_transport_is_active(&self) -> bool {
        self.proof_search
            .borrow()
            .set_builder_forall_transport_is_active(self.proof_scope)
    }

    pub(in crate::verification) fn set_set_builder_forall_transport_active(&self, active: bool) {
        self.proof_search
            .borrow_mut()
            .set_set_builder_forall_transport_active(self.proof_scope, active);
    }

    pub(in crate::verification) fn atomic_fact_proof(
        &self,
        key: &FactString,
    ) -> Option<Rc<SuccessFactProofNode>> {
        self.proof_search
            .borrow()
            .atomic_fact_proof(self.proof_scope, key)
    }

    pub(in crate::verification) fn remember_atomic_fact_proof(
        &self,
        key: FactString,
        result: Rc<SuccessFactProofNode>,
    ) {
        self.proof_search
            .borrow_mut()
            .remember_atomic_fact_proof(self.proof_scope, key, result);
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/verification/proof_search/context_state.rs"]
mod tests;
