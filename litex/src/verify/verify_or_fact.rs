use crate::error::VerifyError;
use crate::execute::Executor;
use crate::fact::OrFact;
use crate::infer::InferResult;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult, StmtUnknown};
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Executor<'a> {
    pub fn verify_or_fact(&mut self, or_fact: &OrFact, verify_state: &VerifyState) -> Result<NonErrStmtExecResult, VerifyError> {
        for fact in or_fact.facts.iter() {
            let result = self.verify_fact(&fact.to_fact(), verify_state)?;
            if result.is_true() {
                return Ok(NonErrStmtExecResult::FactVerifiedByFact(FactVerifiedByFact::new(
                    or_fact.to_string(),
                    fact.to_string(),
                    InferResult::new(),
                    or_fact.line_file,
                    or_fact.line_file,
                )));
            }
        }

        Ok(NonErrStmtExecResult::StmtUnknown(StmtUnknown::new()))
    }
}