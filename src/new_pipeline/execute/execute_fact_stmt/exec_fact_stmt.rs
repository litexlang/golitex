use super::result::ExecFactStmtResult;
use super::VerifyState;
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // Fact stmt pipeline: verify → store + infer.
    // Unknown verify means the asserted fact was not proved; do not store it.
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
        if verify_result.is_unknown() {
            return Err(RuntimeError::Unknown(
                "execute_fact_statement: unable to verify fact".to_string(),
            ));
        }
        let store_and_infer_result = self.store_fact_and_infer(fact)?;
        Ok(ExecFactStmtResult {
            verify_result,
            store_and_infer_result,
        })
    }
}
