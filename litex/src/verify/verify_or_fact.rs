use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::error::VerifyError;
use crate::execute::Executor;
use crate::fact::OrFact;
use crate::infer::InferResult;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult};
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Executor<'a> {
    pub fn verify_or_fact(&mut self, or_fact: &OrFact, verify_state: &VerifyState) -> Result<NonErrStmtExecResult, VerifyError> {
        for fact in or_fact.facts.iter() {
            if self.verify_fact(&fact.to_fact(), verify_state).is_ok() {
                return Ok(NonErrStmtExecResult::FactVerifiedByFact(FactVerifiedByFact::new(
                    or_fact.to_string(),
                    fact.to_string(),
                    InferResult::new(),
                    DEFAULT_LINE_FILE,
                    DEFAULT_LINE_FILE,
                )));
            }
        }

        Err(VerifyError::new(or_fact.to_string(), None, or_fact.line_file_index))
    }
}