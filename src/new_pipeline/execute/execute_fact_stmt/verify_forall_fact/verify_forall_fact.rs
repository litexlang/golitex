use crate::new_pipeline::ast::fact::ForallFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyForallFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn verify_forall_fact(
        &mut self,
        fact: &ForallFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyForallFactResult> {
        let _ = (fact, verify_state);
        Ok(VerifyForallFactResult { _wire: () })
    }
}
