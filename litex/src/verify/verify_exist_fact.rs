use crate::error::VerifyError;
use crate::execute::Executor;
use crate::fact::ExistFact;
use crate::result::NonErrStmtExecResult;
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Executor<'a> {
    pub fn verify_exist_fact(&mut self, exist_fact: &ExistFact, _verify_state: &VerifyState) -> Result<NonErrStmtExecResult, VerifyError> {
        return Err(VerifyError::new(exist_fact.to_string(), vec![], exist_fact.line_file_index()));
    }
}