use crate::new_pipeline::ast::fact::NotForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyNotForallFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Exact ByCache is handled in `verify_fact` before this entry.
    pub fn verify_not_forall_fact(
        &mut self,
        fact: &NotForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyNotForallFactResult>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
