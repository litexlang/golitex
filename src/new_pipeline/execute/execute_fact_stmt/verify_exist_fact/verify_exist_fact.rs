use crate::new_pipeline::ast::fact::ExistFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyExistFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Exact ByCache is handled in `verify_fact` before this entry.
    pub fn verify_exist_fact(
        &mut self,
        fact: &ExistFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyExistFactResult>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
