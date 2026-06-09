use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn exec_fact(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        let result = self.verify_fact_return_err_if_not_true(fact, &VerifyState::new(0, false))?;

        let verified_effects = result.infer_result();
        let mut infer_result =
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(fact.clone())?;
        if verified_effects.contains_added_fact(fact) {
            infer_result.remove_first_verified_statement_for_fact(fact);
        }

        Ok(result.with_infers(infer_result))
    }
}
