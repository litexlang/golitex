//! Isolated-environment well-definedness checks.

use crate::prelude::*;

impl Runtime {
    /// Couples a temporary mathematical environment with one child proof scope.
    /// Parent memo entries remain visible; proofs created from child-only
    /// assumptions disappear when this call returns.
    pub(in crate::verification) fn run_in_local_verification_env<T, E, F>(
        &mut self,
        verify_state: &VerifyState,
        verify: F,
    ) -> Result<T, E>
    where
        F: FnOnce(&mut Self, &VerifyState) -> Result<T, E>,
    {
        let local_verify_state = verify_state.with_child_proof_scope();
        self.run_in_local_env(|runtime| verify(runtime, &local_verify_state))
    }

    pub(in crate::verification) fn run_in_local_verification_env_and_take<T, E, F>(
        &mut self,
        verify_state: &VerifyState,
        verify: F,
    ) -> Result<(T, Environment), E>
    where
        F: FnOnce(&mut Self, &VerifyState) -> Result<T, E>,
    {
        let local_verify_state = verify_state.with_child_proof_scope();
        self.run_in_local_env_and_take(|runtime| verify(runtime, &local_verify_state))
    }
}
