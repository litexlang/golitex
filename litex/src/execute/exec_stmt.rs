use crate::errors::{ExecError, StmtError, UnknownError};
use crate::keywords::UNKNOWN;
use crate::stmt::Stmt;
use crate::result::StmtResult;
use super::Executor;

impl<'a> Executor<'a> {
    /// 建立 verifier，对 fact 做验证，返回 StmtResult。若验证返回 unknown 则转为 UnknownError。
    pub fn stmt(&mut self, stmt: &Stmt) -> Result<StmtResult, StmtError> {
        match stmt {
            Stmt::DefStmt(def_stmt) => self.def_stmt(def_stmt).map_err(StmtError::from),
            Stmt::KnowStmt(know_stmt) => self.know_stmt(know_stmt).map_err(StmtError::from),
            Stmt::Fact(fact) => {
                self.verify_fact_well_defined(fact)?;
                let result = self.verify_fact(fact)?;
                match result {
                        StmtResult::StmtUnknown(_) => Err(StmtError::UnknownError(UnknownError::new(
                            UNKNOWN,
                            stmt.line_file(),
                        ))),
                        _ => return Ok(result),
                    }
                },
            _ => return Err(StmtError::ExecError(ExecError::new("不支持的语句类型", vec![], stmt.line_file()))),
        }
    }
}
