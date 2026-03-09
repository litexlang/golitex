use crate::error::{ExecError, StmtError};
use crate::stmt::Stmt;
use crate::result::StmtResult;
use super::Executor;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn stmt(&mut self, stmt: &Stmt) -> Result<StmtResult, StmtError> {
        match stmt {
            Stmt::DefStmt(def_stmt) => self.def_stmt(def_stmt).map_err(StmtError::from),
            Stmt::KnowStmt(know_stmt) => self.know_stmt(know_stmt).map_err(StmtError::from),
            Stmt::Fact(fact) => self.fact(fact, &mut VerifyState::new(0, false)),
            _ => return Err(StmtError::ExecError(ExecError::new("不支持的语句类型", vec![], stmt.line_file()))),
        }
    }
}
