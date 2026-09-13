use crate::new_pipeline::ast::fact::AndFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyAndFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn verify_and_fact(
        &mut self,
        fact: &AndFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAndFactResult> {
        let _ = (fact, verify_state);
        Ok(VerifyAndFactResult { _wire: () })
    }
}
