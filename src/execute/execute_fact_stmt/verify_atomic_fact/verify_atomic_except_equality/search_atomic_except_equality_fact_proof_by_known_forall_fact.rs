//! Non-equality atomic → known forall.
//!
//! Thin entry: delegates to `search_atomic_fact_proof_by_known_forall_fact`
//! (same pipeline as `=`). See that file for stages and a worked example.
//!
//! Called from `search_atomic_except_equality_fact_proof` when
//! the shared DefinitionAndForall stage admits it with a restricted premise state.

use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::SearchProofByKnownForallFact;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        self.search_atomic_fact_proof_by_known_forall_fact(fact, verify_state)
    }
}
