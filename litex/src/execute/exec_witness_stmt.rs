use super::Runtime;
use crate::error::RuntimeError;
use crate::result::NonErrStmtExecResult;
use crate::stmt::witness_stmt::{WitnessExistFact, WitnessNonemptySet};
use crate::stmt::Stmt;

impl<'a> Runtime<'a> {
    pub fn exec_witness_exist_fact(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::WitnessExistFact(stmt.clone()))
    }

    pub fn exec_witness_nonempty_set(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        Self::stmt_unsupported(Stmt::WitnessNonemptySet(stmt.clone()))
    }
}
