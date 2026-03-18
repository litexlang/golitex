use crate::error::StmtError;
use crate::stmt::witness_stmt::{WitnessExistFact, WitnessNonemptySet};
use crate::result::NonErrStmtExecResult;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn exec_witness_exist_fact(&mut self, stmt: &WitnessExistFact) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_witness_nonempty_set(&mut self, stmt: &WitnessNonemptySet) -> Result<NonErrStmtExecResult, StmtError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }
}
