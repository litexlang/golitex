use super::result::ExecFactStmtResult;
use super::VerifyState;
use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Fact stmt inside the exec_stmt temp env: verify → store on current top.
    // Err(VerifyFactResult) = soft miss (maps to ExecStmtResult::Failed).
    pub(in crate::new_pipeline::execute) fn execute_fact_statement(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<Result<ExecFactStmtResult, VerifyFactResult>> {
        let verify_state = VerifyState {
            can_use_forall_fact: true,
            can_use_known_algebraic_rewrite: true,
            store_well_defined_fact: true,
        };
        let verify_result = self.verify_fact(fact, verify_state)?;
        if verify_result.is_failed() {
            return Ok(Err(verify_result));
        }
        let store_and_infer_result = self.store_fact_and_infer(fact)?;
        Ok(Ok(ExecFactStmtResult {
            verify_result,
            store_and_infer_result,
        }))
    }
}
