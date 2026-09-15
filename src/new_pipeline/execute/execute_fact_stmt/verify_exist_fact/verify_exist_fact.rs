use crate::new_pipeline::ast::fact::ExistFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyExistFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // exist-fact search is still draft-only.
    pub fn verify_exist_fact(
        &mut self,
        _fact: &ExistFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<VerifyExistFactResult>> {
        Ok(None)
    }
}
