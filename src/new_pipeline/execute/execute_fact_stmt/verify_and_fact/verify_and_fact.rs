use crate::new_pipeline::ast::fact::AndFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyAndFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // and/or/chain/exist/forall search is still draft-only.
    pub fn verify_and_fact(
        &mut self,
        _fact: &AndFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyAndFactResult>> {
        Ok(None)
    }
}
