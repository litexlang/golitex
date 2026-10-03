use super::result::{ExecFactStmtResult, ExecFactStmtSuccessResult};
use super::VerifyState;
use crate::ast::fact::Fact;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Fact stmt inside the exec_stmt temp env: verify → store on current top.
    // Failed soft miss stays in ExecFactStmtResult::Failed (temp discarded by exec_stmt).
    pub(in crate::execute) fn execute_fact_statement(
        &mut self,
        fact: &Fact,
    ) -> RuntimeResult<ExecFactStmtResult> {
        let verify_state = VerifyState::top_level();
        let verify_result = self.verify_fact(fact, verify_state)?;
        if verify_result.is_failed() {
            return Ok(ExecFactStmtResult::Failed(verify_result));
        }
        let store_and_infer_result = self.store_fact_and_infer(fact, crate::execute::execute_fact_stmt::VerifyState::top_level())?;
        Ok(ExecFactStmtResult::Success(ExecFactStmtSuccessResult {
            verify_result,
            store_and_infer_result,
        }))
    }
}
