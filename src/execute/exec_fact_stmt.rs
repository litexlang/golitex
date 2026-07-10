use crate::prelude::*;
use std::result::Result;

impl Runtime {
    pub fn exec_fact(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        self.exec_fact_stmt_verify_well_definedness(fact)?;
        let result = self.exec_fact_stmt_verify_process(fact)?;
        let infer_result = self.exec_fact_stmt_affect_environment(fact, &result)?;

        Ok(result.with_infers(infer_result))
    }

    fn exec_fact_stmt_verify_well_definedness(&mut self, fact: &Fact) -> Result<(), RuntimeError> {
        self.verify_fact_well_defined(fact, &VerifyState::new(0, false))
    }

    fn exec_fact_stmt_verify_process(&mut self, fact: &Fact) -> Result<StmtResult, RuntimeError> {
        self.verify_fact_return_err_if_not_true(fact, &VerifyState::new(0, false))
    }

    fn exec_fact_stmt_affect_environment(
        &mut self,
        fact: &Fact,
        result: &StmtResult,
    ) -> Result<InferResult, RuntimeError> {
        let verification_store_facts = result.infer_result();
        let mut infer_result =
            self.verify_well_defined_and_store_and_infer_with_default_verify_state(fact.clone())?;
        if verification_store_facts.contains_added_fact(fact) {
            infer_result.remove_first_verified_statement_for_fact(fact);
        }

        Ok(infer_result)
    }
}
