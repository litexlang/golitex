use crate::error::StmtError;
use crate::stmt::witness_stmt::{WitnessExistFact, WitnessNonemptySet};
use crate::result::NonErrStmtResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_witness_exist_fact(&mut self, stmt: &WitnessExistFact) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }

    pub fn exec_witness_nonempty_set(&mut self, stmt: &WitnessNonemptySet) -> Result<NonErrStmtResult, StmtError> {
        Self::stmt_unsupported(stmt.line_file_index)
    }
}
