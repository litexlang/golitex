//! Proof-result reuse for one explicit verification search.

use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
    /// Reuses a completed atomic proof visible from the current proof scope.
    pub fn verification_result_from_proof_search_memo(
        &self,
        fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Option<ProveFactResult> {
        let key = fact.to_string();
        verify_state.atomic_fact_proof(&key).map(|source| {
            SuccessProveFactResult::new_with_reused_verification(
                fact.clone().into(),
                SuccessInferResult::new(),
                source,
            )
            .into()
        })
    }

    /// Remembers a successful proof in the current proof scope without storing the fact.
    pub fn remember_successful_atomic_fact_for_proof_search(
        &mut self,
        fact: &AtomicFact,
        mut result: ProveFactResult,
        verify_state: &VerifyState,
    ) -> ProveFactResult {
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
        if verify_state.atomic_fact_proof(&key).is_some() {
            return result;
        }

        let source = result
            .factual_success()
            .expect("successful atomic fact verification must return a factual result")
            .verification
            .clone();
        verify_state.remember_atomic_fact_proof(key, source);
        result
    }
}
