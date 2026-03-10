use crate::error::{StmtError, UnknownError};
use crate::fact::Fact;
use crate::common::keywords::UNKNOWN;
use crate::result::StmtResult;
use crate::verify::VerifyState;
use super::Executor;
use std::result::Result;
use crate::error::VerifyFactError;

impl<'a> Executor<'a> {
    pub fn fact(&mut self, fact: &Fact, verify_state: &mut VerifyState) -> Result<StmtResult, StmtError> {
        self.verify_fact_well_defined(fact, verify_state)?;
        let result = match fact {
            Fact::AtomicFact(atomic_fact) => self.verify_atomic_fact(atomic_fact, verify_state),
            _ => Err(VerifyFactError::new("verify_fact: NOT IMPLEMENTED YET", vec![], None)),
        };
        let result = match result {
            Ok(StmtResult::StmtUnknown(_)) => {
                return Err(StmtError::UnknownError(UnknownError::new(
                    UNKNOWN,
                    fact.line_file(),
                )))
            }
            Ok(r) => r,
            Err(e) => return Err(e.into()),
        };

        self.store_fact_without_well_defined_verified(fact)?;

        Ok(result)
    }
}