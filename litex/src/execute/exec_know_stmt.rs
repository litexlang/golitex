use crate::errors::ExecError;
use crate::stmt::know_stmt::KnowStmt;
use crate::result::StmtResult;
use crate::result::NonFactualStmtSuccess;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn know_stmt(&mut self, know_stmt: &KnowStmt) -> Result<StmtResult, ExecError> {
        for fact in know_stmt.facts.iter() {
            self.validate_and_store_fact(fact)?;
        }
        Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(know_stmt.to_string(), know_stmt.line_file_index)))
    }
}
