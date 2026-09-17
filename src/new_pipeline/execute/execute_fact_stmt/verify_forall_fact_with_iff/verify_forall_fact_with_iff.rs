use crate::new_pipeline::ast::fact::ForallFactWithIff;
use crate::new_pipeline::execute::execute_fact_stmt::verify_forall_fact_with_iff::VerifyForallFactWithIffResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // forall-with-iff search is still draft-only.
    pub fn verify_forall_fact_with_iff(
        &mut self,
        _fact: &ForallFactWithIff,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyForallFactWithIffResult>> {
        Ok(None)
    }
}
