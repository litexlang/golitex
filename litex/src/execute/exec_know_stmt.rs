use crate::error::ExecError;
use crate::stmt::know_stmt::KnowStmt;
use crate::result::StmtResult;
use crate::result::NonFactualStmtSuccess;
use super::Executor;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn know_stmt(&mut self, know_stmt: &KnowStmt) -> Result<StmtResult, ExecError> {
        for fact in know_stmt.facts.iter() {
            self.verify_fact_well_defined_and_store(fact, &mut VerifyState::new(0, false))?;
        }
        Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(know_stmt.to_string(), know_stmt.line_file_index)))
    }
}
