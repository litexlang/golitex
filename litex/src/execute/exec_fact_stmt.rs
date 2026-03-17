use crate::error::{StmtError, UnknownError};
use crate::fact::Fact;
use crate::result::NonErrStmtExecResult;
use crate::verify::VerifyState;
use super::Executor;
use std::result::Result;


impl<'a> Executor<'a> {
    pub fn exec_fact(&mut self, fact: &Fact) -> Result<NonErrStmtExecResult, StmtError> {
        let result = self.verify_fact(fact, &VerifyState::new(0, false))?;
        let result = match result {
            NonErrStmtExecResult::StmtUnknown(_) => {
                return Err(StmtError::UnknownError(UnknownError::new(
                    fact.to_string(),
                    fact.line_file(),
                    None,
                )))
            }
            r => r,
        };

        self.store_fact_without_well_defined_verified_and_infer(fact)?;

        Ok(result)
    }
}