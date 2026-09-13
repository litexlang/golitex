use super::exec_stmt_result::{ExecDefinitionStmtResult, ExecStmtResult};
use crate::new_pipeline::ast::stmt::{DefinitionStmt, Stmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    // Match stmt kind, then run the dedicated exec_xxx_stmt pipeline.
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> RuntimeResult<ExecStmtResult> {
        match stmt {
            Stmt::Fact(fact) => Ok(ExecStmtResult::Fact(self.execute_fact_statement(fact)?)),
            Stmt::Definition(DefinitionStmt::LetObjStmt(let_stmt)) => {
                Ok(ExecStmtResult::Definition(ExecDefinitionStmtResult::LetObj(
                    self.exec_let_obj(let_stmt)?,
                )))
            }
            Stmt::Definition(DefinitionStmt::DefPropStmt(def_prop)) => {
                Ok(ExecStmtResult::Definition(ExecDefinitionStmtResult::DefProp(
                    self.exec_def_prop_stmt(def_prop)?,
                )))
            }
            _ => Err(RuntimeError::Unsupported(
                "new_pipeline exec_stmt: only Fact, let, and prop are wired for the tracer"
                    .to_string(),
            )),
        }
    }
}
