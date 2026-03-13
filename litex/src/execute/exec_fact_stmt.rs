use crate::error::{StmtError, UnknownError};
use crate::fact::Fact;
use crate::result::NonErrStmtResult;
use crate::verify::VerifyState;
use super::Executor;
use std::result::Result;


impl<'a> Executor<'a> {
    pub fn exec_fact(&mut self, fact: &Fact, verify_state: &VerifyState) -> Result<NonErrStmtResult, StmtError> {
        let result = self.verify_fact(fact, verify_state)?;
        let result = match result {
            NonErrStmtResult::StmtUnknown(_) => {
                return Err(StmtError::UnknownError(UnknownError::new(
                    fact.to_string().as_str(),
                    fact.line_file(),
                )))
            }
            r => r,
        };

        self.store_fact_without_well_defined_verified(fact)?;

        Ok(result)
    }
}