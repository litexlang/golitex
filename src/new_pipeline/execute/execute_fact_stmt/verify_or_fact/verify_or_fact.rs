use crate::new_pipeline::ast::fact::OrFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyOrFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Exact ByCache is handled in `verify_fact` before this entry.
    pub fn verify_or_fact(
        &mut self,
        _fact: &OrFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyOrFactResult>> {
        Ok(None)
    }
}
