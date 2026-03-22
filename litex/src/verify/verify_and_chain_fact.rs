use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::error::VerifyError;
use crate::execute::Executor;
use crate::fact::{AndFact, ChainFact, Fact};
use crate::infer::InferResult;
use crate::result::{FactVerifiedByFact, NonErrStmtExecResult};
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Executor<'a> {
    pub fn verify_and_fact(
        &mut self,
        and_fact: &AndFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let mut verify_what = Vec::with_capacity(and_fact.facts.len());
        for fact in &and_fact.facts {
            let result = self.verify_fact(&Fact::AtomicFact(fact.clone()), verify_state)?;
            if !result.is_true() {
                return Ok(result);
            }
            verify_what.push(fact.to_string());
        }
        Ok(NonErrStmtExecResult::FactVerifiedByFact(
            FactVerifiedByFact::new(
                and_fact.to_string(),
                format!("{} are verified", verify_what.join(", ")),
                InferResult::new(),
                DEFAULT_LINE_FILE.clone(),
                DEFAULT_LINE_FILE.clone(),
            ),
        ))
    }

    pub fn verify_chain_fact(
        &mut self,
        chain_fact: &ChainFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        let facts = chain_fact
            .facts()
            .map_err(|e| VerifyError::new(e.to_string(), None, DEFAULT_LINE_FILE.clone()))?;
        let mut verify_what = Vec::with_capacity(facts.len());
        for fact in &facts {
            let result = self.verify_fact(&Fact::AtomicFact(fact.clone()), verify_state)?;
            if !result.is_true() {
                return Ok(result);
            }

            verify_what.push(fact.to_string());
        }
        Ok(NonErrStmtExecResult::FactVerifiedByFact(
            FactVerifiedByFact::new(
                chain_fact.to_string(),
                format!("{} are verified", verify_what.join(", ")),
                InferResult::new(),
                DEFAULT_LINE_FILE.clone(),
                DEFAULT_LINE_FILE.clone(),
            ),
        ))
    }
}
