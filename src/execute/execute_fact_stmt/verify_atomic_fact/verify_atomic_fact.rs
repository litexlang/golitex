use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // EqualFact → Equality; other atomics → AtomicExceptEquality.
    // Both branches return VerifyFactResult so Unknown stays Ok, not Err.
    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => self.verify_equal_fact(equal_fact, verify_state),
            _ => self.verify_atomic_except_equality(fact, verify_state),
        }
    }
}
