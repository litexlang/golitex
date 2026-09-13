use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::VerifyAtomicFactResult;

impl Runtime {
    // EqualFact → Equality; other atomics → NonEquational.
    pub fn verify_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyAtomicFactResult> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => Ok(VerifyAtomicFactResult::Equality(
                self.verify_equal_fact(equal_fact, verify_state)?,
            )),
            _ => Ok(VerifyAtomicFactResult::NonEquational(
                self.verify_non_equational_fact(fact, verify_state)?,
            )),
        }
    }
}
