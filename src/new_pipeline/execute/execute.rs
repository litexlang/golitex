use super::exec_stmt_result::{
    ExecDefinitionStmtResult, ExecStmtResult,
};
use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::ast::stmt::{DefinitionStmt, Stmt};
use crate::new_pipeline::execute::execute_fact_stmt::ExecFactStmtResult2;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};

impl Runtime {
    pub fn exec_stmt(&mut self, stmt: &Stmt) -> RuntimeResult<ExecStmtResult> {
        match stmt {
            Stmt::Fact(fact) => Ok(ExecStmtResult::Fact(self.exec_fact(fact)?)),
            Stmt::Definition(DefinitionStmt::LetObjStmt(let_stmt)) => {
                Ok(ExecStmtResult::Definition(ExecDefinitionStmtResult::LetObj(
                    self.exec_let_obj(let_stmt)?,
                )))
            }
            _ => Err(RuntimeError::Unsupported(
                "new_pipeline exec_stmt: only Fact and let are wired for the tracer".to_string(),
            )),
        }
    }

    fn exec_fact(&mut self, fact: &Fact) -> RuntimeResult<ExecFactStmtResult2> {
        match fact {
            Fact::AtomicFact(AtomicFact::EqualFact(equal)) => {
                self.exec_native_equal_fact(equal)
            }
            _ => Err(RuntimeError::Unsupported(
                "new_pipeline exec_fact: only equality facts are wired for the tracer".to_string(),
            )),
        }
    }
}
