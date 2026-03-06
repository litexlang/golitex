use crate::errors::ExecError;
use crate::stmt::Stmt;
use crate::executor::Executor;
use crate::stmt_result::StmtResult;

impl<'a> Executor<'a> {
    pub fn stmt(&mut self, stmt: Stmt) -> Result<StmtResult, ExecError> {
        match stmt {
            Stmt::DefStmt(def_stmt) => self.def_stmt(def_stmt),
            _ => Err(ExecError::new("不支持的语句类型", stmt.line_file())),
        }
    }
}