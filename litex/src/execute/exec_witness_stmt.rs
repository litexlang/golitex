use super::Runtime;
use crate::error::RuntimeError;
use crate::result::NonErrStmtExecResult;
use crate::stmt::witness_stmt::{WitnessExistFact, WitnessNonemptySet};

impl<'a> Runtime<'a> {
    pub fn exec_witness_exist_fact(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }

    pub fn exec_witness_nonempty_set(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(stmt.stmt_type_name(), stmt.line_file)
    }
}
