use crate::error::VerifyError;
use crate::execute::Executor;
use crate::fact::OrFact;
use crate::result::NonErrStmtResult;
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Executor<'a> {
    pub fn verify_or_fact(&mut self, or_fact: &OrFact, _verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        return Err(VerifyError::new(or_fact.to_string(), vec![], or_fact.line_file_index));
    }
}