use crate::ast::fact::AtomicFact;
use crate::execute::execute_fact_stmt::verify_atomic_fact::AtomicExceptEqualityFactSearchedProof;
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof(
        &mut self,
        fact: &AtomicFact,
        state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        use super::super::AtomicFactSearchedProof;
        Ok(match self.search_atomic_fact(fact, state)? {
            Some(AtomicFactSearchedProof::AtomicExceptEquality(p)) => Some(p),
            None => None,
            Some(AtomicFactSearchedProof::Equality(_)) => unreachable!("non-equality dispatch"),
        })
    }
}
