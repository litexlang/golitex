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
        let verify_state = VerifyState {
            can_use_builtin_rule: true,
            can_use_def_and_known_forall_and_known_strategy: true,
            can_use_rewrite: true,
            store_well_defined_fact: true,
};
        let verify_result = self.verify_fact(fact, verify_state)?;
        if verify_result.is_failed() {
            return Ok(ExecFactStmtResult::Failed(verify_result));
        }
        let store_and_infer_result = self.store_fact_and_infer(fact)?;
        Ok(ExecFactStmtResult::Success(ExecFactStmtSuccessResult {
            verify_result,
            store_and_infer_result,
        }))
    }
}
