use crate::error::ExecError;
use crate::stmt::know_stmt::KnowStmt;
use crate::result::NonErrStmtResult;
use crate::result::NonFactualStmtSuccess;
use super::Executor;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn exec_know_stmt(&mut self, know_stmt: &KnowStmt) -> Result<NonErrStmtResult, ExecError> {
        for fact in know_stmt.facts.iter() {
            self.verify_fact_well_defined_and_store_and_infer(fact, &VerifyState::new(0, false))?;
        }
        Ok(NonErrStmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(know_stmt.to_string(), know_stmt.line_file_index)))
    }
}
