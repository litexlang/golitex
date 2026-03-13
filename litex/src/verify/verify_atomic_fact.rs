use crate::fact::AtomicFact;
use crate::execute::Executor;
use crate::error::VerifyError;
use crate::result::NonErrStmtResult;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn verify_atomic_fact(&mut self, atomic_fact: &AtomicFact, verify_state: &VerifyState) -> Result<NonErrStmtResult, VerifyError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.verify_equal_fact(equal_fact, verify_state),
            _ => self.verify_non_equational_atomic_fact(atomic_fact, verify_state),
        }
    }
}
