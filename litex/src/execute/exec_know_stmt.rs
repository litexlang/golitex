use crate::error::ExecError;
use crate::stmt::know_stmt::KnowStmt;
use crate::result::NonErrStmtExecResult;
use crate::result::NonFactualStmtSuccess;
use super::Executor;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn exec_know_stmt(&mut self, know_stmt: &KnowStmt) -> Result<NonErrStmtExecResult, ExecError> {
        for fact in know_stmt.facts.iter() {
            self.verify_fact_well_defined_and_store_and_infer(fact, &VerifyState::new(0, false)).map_err(|e| ExecError::new(know_stmt.stmt_type_name(), know_stmt.to_string(), Some(e.into()), know_stmt.line_file_index))?;
        }
        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(know_stmt.to_string(), know_stmt.line_file_index)))
    }
}
