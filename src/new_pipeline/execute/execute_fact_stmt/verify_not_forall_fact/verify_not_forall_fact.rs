use crate::new_pipeline::ast::fact::NotForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_not_forall_fact::VerifyNotForallFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // not-forall search is still draft-only.
    pub fn verify_not_forall_fact(
        &mut self,
        _fact: &NotForallFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyNotForallFactResult>> {
        Ok(None)
    }
}
