use crate::error::{StmtError};
use crate::fact::Fact;
use crate::result::NonErrStmtResult;
use crate::verify::VerifyState;
use std::result::Result;
use crate::error::VerifyError;
use crate::execute::Executor;

impl<'a> Executor<'a> {
    pub fn verify_fact(&mut self, fact: &Fact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {   
        if !verify_state.well_defined_already_verified {
            if let Err(e) = self.verify_fact_well_defined(fact, verify_state) {
                return Err(VerifyError::new(fact.to_string().as_str(), vec![StmtError::WellDefinedError(e)], fact.line_file()));
            }
        }
        match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact(atomic_fact, verify_state),
            _ => Err(VerifyError::new("verify_fact: NOT IMPLEMENTED YET", vec![], None)),
        }
    }
}