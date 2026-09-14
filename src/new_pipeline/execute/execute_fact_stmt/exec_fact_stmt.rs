use super::result::ExecFactStmtResult;
use super::VerifyState;
use crate::new_pipeline::ast::fact::Fact;
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
        let store_and_infer_result = self.store_fact_then_infer(fact, &verify_result)?;
        Ok(ExecFactStmtResult {
            verify_result,
            store_and_infer_result,
        })
    }
}
