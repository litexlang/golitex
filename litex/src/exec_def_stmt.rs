use crate::errors::ExecError;
use crate::definition_stmt::DefStmt;
use crate::executor::Executor;
use crate::definition_stmt::DefPropStmt;
use crate::stmt_result::StmtResult;
use crate::stmt_success::StmtSuccess;
use crate::stmt_success::NonFactualStmtSuccess;

impl<'a> Executor<'a> {
    pub fn def_stmt(&mut self, def_stmt: DefStmt) -> Result<StmtResult, ExecError> {
        match def_stmt {
            DefStmt::DefPropStmt(def_prop_stmt) => self.def_prop_stmt(def_prop_stmt),
            _ => Err(ExecError::new("不支持的定义语句类型")),
        }
    }

    pub fn def_prop_stmt(&mut self, def_prop_stmt: DefPropStmt) -> Result<StmtResult, ExecError> {
        let stmt_str = def_prop_stmt.to_string();
        let line_file_index = def_prop_stmt.line_file_index;
        self.validate_name_and_store_def_prop(def_prop_stmt)?;
        Ok(StmtResult::StmtSuccess(StmtSuccess::NonFactualStmtSuccess(NonFactualStmtSuccess::new(stmt_str, line_file_index))))
    }
}