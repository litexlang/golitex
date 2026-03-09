use crate::error::{StmtError, UnknownError};
use crate::fact::Fact;
use crate::common::keywords::UNKNOWN;
use crate::result::StmtResult;
use super::Executor;
use std::result::Result;

impl<'a> Executor<'a> {
    pub fn fact(&mut self, fact: &Fact) -> Result<StmtResult, StmtError> {
        self.verify_fact_well_defined(fact)?;
        let result = self.verify_fact(fact)?;
        match result {
            StmtResult::StmtUnknown(_) => return Err(StmtError::UnknownError(UnknownError::new(
                UNKNOWN,
                fact.line_file(),
            ))),
            _ => (),
        }

        self.store_fact(fact)?;

        Ok(result)
    }
}