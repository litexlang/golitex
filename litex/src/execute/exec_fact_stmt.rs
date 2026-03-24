use super::Runtime;
use crate::error::RuntimeError;
use crate::fact::Fact;
use crate::result::NonErrStmtExecResult;
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Runtime<'a> {
    pub fn exec_fact(&mut self, fact: &Fact) -> Result<NonErrStmtExecResult, RuntimeError> {
        let result = self.verify_fact_return_err_if_not_true(fact, &VerifyState::new(0, false))?;

        let infer_result = self.store_fact_without_well_defined_verified_and_infer(fact)?;

        Ok(result.with_infers(infer_result))
    }
}
