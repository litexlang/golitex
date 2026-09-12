use super::result::{ExecFactStmtResult, StoreFactAndInferResult2};
use super::verify_atomic_fact::VerifyAtomicFactResult2;
use super::verify_fact_result::VerifyFactResult2;
use super::VerifyState2;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::prelude::{AtomicFact, Fact};

impl Runtime {
    pub fn execute_fact_statement2(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<ExecFactStmtResult> {
        let verify_state = VerifyState2 {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };
        let verify_result = self.verify_fact2(fact, verify_state)?;
        let store_and_infer_result = self.store_fact_then_infer(&verify_result)?;
        Ok(ExecFactStmtResult {
            verify_result,
            store_and_infer_result,
        })
    }

    pub fn verify_fact2(
        &mut self,
        fact: &Fact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<VerifyFactResult2> {
        match fact {
            Fact::AtomicFact(fact) => Ok(VerifyFactResult2::AtomicFact(Box::new(
                self.verify_atomic_fact2(fact, verify_state)?,
            ))),
            _ => Err(RuntimeError::Unknown(
                "verify_fact2: only atomic facts are wired for the tracer".to_string(),
            )),
        }
    }

    pub fn verify_atomic_fact2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<VerifyAtomicFactResult2> {
        match fact {
            AtomicFact::EqualFact(equal_fact) => Ok(VerifyAtomicFactResult2::Equality(
                self.verify_equal_fact2(equal_fact, verify_state)?,
            )),
            _ => Ok(VerifyAtomicFactResult2::NonEquationalAtomicFact(
                self.verify_non_equational_atomic_fact2(fact, verify_state)?,
            )),
        }
    }

    fn store_fact_then_infer(
        &mut self,
        verify_result: &VerifyFactResult2,
    ) -> RuntimeResult<StoreFactAndInferResult2> {
        let _ = verify_result;
        // Global ExecEnv write comes later; return an empty effect mirror for now.
        Ok(StoreFactAndInferResult2::empty())
    }
}
