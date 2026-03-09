use crate::error::ExecError;
use crate::stmt::definition_stmt::{DefLetStmt, DefPropStmt, DefStmt, DefStructStmt};
use crate::stmt::define_algorithm_stmt::DefAlgoStmt;
use crate::result::StmtResult;
use crate::result::NonFactualStmtSuccess;
use super::Executor;

impl<'a> Executor<'a> {
    pub fn def_stmt(&mut self, def_stmt: &DefStmt) -> Result<StmtResult, ExecError> {
        match def_stmt {
            DefStmt::DefPropStmt(def_prop_stmt) => self.def_prop_stmt(def_prop_stmt),
            DefStmt::DefLetStmt(def_let_stmt) => self.def_let_stmt(def_let_stmt),
            DefStmt::DefStructStmt(def_struct_stmt) => self.def_struct_stmt(def_struct_stmt),
            DefStmt::DefAlgoStmt(def_algo_stmt) => self.def_algo_stmt(def_algo_stmt),
            _ => Err(ExecError::new("不支持的定义语句类型", vec![], def_stmt.line_file())),
        }
    }

    pub fn def_prop_stmt(&mut self, def_prop_stmt: &DefPropStmt) -> Result<StmtResult, ExecError> {
        self.validate_name_and_store_def_prop(def_prop_stmt)?;
        Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_prop_stmt.to_string(), def_prop_stmt.line_file_index)))
    }

    pub fn def_let_stmt(&mut self, def_let_stmt: &DefLetStmt) -> Result<StmtResult, ExecError> {
        self.validate_name_and_store_atom_name(&def_let_stmt.param_def, def_let_stmt.line_file_index)?;
        for fact in def_let_stmt.facts.iter() {
            self.store_fact(fact)?;
        }
        Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_let_stmt.to_string(), def_let_stmt.line_file_index)))
    }


    pub fn def_struct_stmt(&mut self, def_struct_stmt: &DefStructStmt) -> Result<StmtResult, ExecError> {
        self.validate_name_and_store_def_struct(def_struct_stmt)?;
        Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_struct_stmt.to_string(), def_struct_stmt.line_file_index())))
    }

    pub fn def_algo_stmt(&mut self, def_algo_stmt: &DefAlgoStmt) -> Result<StmtResult, ExecError> {
        self.validate_name_and_store_def_algo(def_algo_stmt)?;
        Ok(StmtResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(def_algo_stmt.to_string(), def_algo_stmt.line_file_index)))
    }
}
