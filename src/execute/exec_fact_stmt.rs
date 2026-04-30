use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn exec_fact(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        let result = self.verify_fact_return_err_if_not_true(fact, &VerifyState::new(0, false))?;

        let infer_result =
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(fact.clone())?;

        Ok(result.with_infers(infer_result))
    }
}
