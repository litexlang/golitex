use crate::new_pipeline::ast::fact::ForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyForallFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // forall-fact search is still draft-only.
    pub fn verify_forall_fact(
        &mut self,
        _fact: &ForallFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyForallFactResult>> {
        Ok(None)
    }
}
