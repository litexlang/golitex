use crate::error::{StmtError, VerifyError};
use crate::execute::Executor;
use crate::fact::{AndFact, ChainFact, Fact};
use crate::result::{FactVerifiedByFact, NonErrStmtResult};
use crate::verify::VerifyState;
use std::result::Result;

impl<'a> Executor<'a> {
    pub fn verify_and_fact(&mut self, and_fact: &AndFact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        for fact in &and_fact.facts {
            if let Err(e) = self.verify_fact(&Fact::AtomicFact(fact.clone()), verify_state) {
                return Err(VerifyError::new(fact.to_string(), vec![StmtError::VerifyError(e)], and_fact.line_file_index()));
            }
        }
        Ok(NonErrStmtResult::FactVerifiedByFact(FactVerifiedByFact::new(
            and_fact.to_string(),
            "each constituent fact verified".to_string(),
            and_fact.line_file_index(),
        )))
    }

    pub fn verify_chain_fact(&mut self, chain_fact: &ChainFact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        let facts = chain_fact.facts().map_err(|e| VerifyError::new(e.to_string(), vec![], None))?;
        for fact in &facts {
            if let Err(e) = self.verify_fact(&Fact::AtomicFact(fact.clone()), verify_state) {
                return Err(e);
            }
        }
        Ok(NonErrStmtResult::FactVerifiedByFact(FactVerifiedByFact::new(
            chain_fact.to_string(),
            "each constituent fact verified".to_string(),
            chain_fact.line_file_index(),
        )))
    }
}