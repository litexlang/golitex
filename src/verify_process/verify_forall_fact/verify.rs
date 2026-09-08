use crate::prelude::*;

impl Runtime {
    pub fn verify_forall_fact(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> Result<VerifyForallFactResult, RuntimeError> {
        self.execute_in_local_scope(|runtime| {})
    }
}
