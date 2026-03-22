use crate::error::VerifyError;
use crate::execute::Runtime;
use crate::fact::AtomicFact;
use crate::result::NonErrStmtExecResult;
use crate::verify::VerifyState;

impl<'a> Runtime<'a> {
    pub fn verify_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        verify_state: &VerifyState,
    ) -> Result<NonErrStmtExecResult, VerifyError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.verify_equal_fact(equal_fact, verify_state),
            _ => self.verify_non_equational_atomic_fact(atomic_fact, verify_state),
        }
    }
}
