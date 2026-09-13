use crate::new_pipeline::ast::fact::OrFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyOrFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn verify_or_fact(
        &mut self,
        fact: &OrFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyOrFactResult> {
        let _ = (fact, verify_state);
        Ok(VerifyOrFactResult { _wire: () })
    }
}
