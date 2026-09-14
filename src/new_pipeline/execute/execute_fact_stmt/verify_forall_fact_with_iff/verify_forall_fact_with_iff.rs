use crate::new_pipeline::ast::fact::ForallFactWithIff;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyForallFactWithIffResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Exact ByCache is handled in `verify_fact` before this entry.
    pub fn verify_forall_fact_with_iff(
        &mut self,
        fact: &ForallFactWithIff,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyForallFactWithIffResult>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
