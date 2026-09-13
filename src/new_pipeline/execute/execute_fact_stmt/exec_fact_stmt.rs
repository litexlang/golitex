use super::result::{ExecFactStmtResult, StoreFactAndInferResult};
use super::verify_atomic_fact::VerifyAtomicFactResult;
use super::verify_fact_result::VerifyFactResult;
use super::VerifyState;
use crate::new_pipeline::ast::fact::{EqualFact, Fact};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Fact stmt pipeline: verify → store + infer.
    pub fn execute_fact_statement(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<ExecFactStmtResult> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };
        let verify_result = self.verify_fact(fact, verify_state)?;
        let store_and_infer_result = self.store_fact_then_infer(&verify_result)?;
        Ok(ExecFactStmtResult {
            verify_result,
            store_and_infer_result,
        })
    }

    fn store_fact_then_infer(
        &mut self,
        verify_result: &VerifyFactResult,
    ) -> RuntimeResult<StoreFactAndInferResult> {
        match verify_result {
            VerifyFactResult::AtomicFact(atomic) => match atomic.as_ref() {
                VerifyAtomicFactResult::Equality(eq) => self.store_equal_fact_then_infer(&eq.fact),
                // Non-equality fact store waits on known-atomic search / general fact memory.
                _ => Ok(StoreFactAndInferResult::empty()),
            },
            _ => Ok(StoreFactAndInferResult::empty()),
        }
    }

    fn store_equal_fact_then_infer(
        &mut self,
        fact: &EqualFact,
    ) -> RuntimeResult<StoreFactAndInferResult> {
        self.top_exec_env_mut()
            .store_native_equal_fact(fact.clone());
        Ok(StoreFactAndInferResult {
            stored_fact_ids: vec![fact.fact_id],
        })
    }
}
