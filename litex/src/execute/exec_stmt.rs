use crate::error::{ExecError, StmtError};
use crate::stmt::Stmt;
use crate::result::NonErrStmtResult;
use super::Executor;
use crate::verify::VerifyState;

impl<'a> Executor<'a> {
    pub fn stmt(&mut self, stmt: &Stmt) -> Result<NonErrStmtResult, StmtError> {
        match stmt {
            Stmt::DefLetStmt(d) => self.def_let_stmt(d).map_err(StmtError::from),
            Stmt::DefPropStmt(d) => self.def_prop_stmt(d).map_err(StmtError::from),
            Stmt::DefPropWithoutMeaningStmt(d) => self.def_prop_without_meaning_stmt(d).map_err(StmtError::from),
            Stmt::HaveObjInNonemptySetStmt(d) => self.have_obj_in_nonempty_set_or_param_type_stmt(d).map_err(StmtError::from),
            Stmt::HaveObjEqualStmt(d) => self.have_obj_equal_stmt(d).map_err(StmtError::from),
            Stmt::HaveExistObjStmt(d) => self.have_exist_obj_stmt(d).map_err(StmtError::from),
            Stmt::HaveFnEqualStmt(d) => self.have_fn_equal_stmt(d).map_err(StmtError::from),
            Stmt::HaveFnEqualCaseByCaseStmt(d) => self.have_fn_equal_case_by_case_stmt(d).map_err(StmtError::from),
            Stmt::DefStructWithFieldsStmt(d) => self.def_struct_with_fields_stmt(d).map_err(StmtError::from),
            Stmt::DefStructWithNoFieldStmt(d) => self.def_struct_with_no_field_stmt(d).map_err(StmtError::from),
            Stmt::DefAlgoStmt(d) => self.def_algo_stmt(d).map_err(StmtError::from),
            Stmt::KnowStmt(know_stmt) => self.exec_know_stmt(know_stmt).map_err(StmtError::from),
            Stmt::Fact(fact) => self.exec_fact(fact, &VerifyState::new(0, false)),
            _ => return Err(StmtError::ExecError(ExecError::new("不支持的语句类型", vec![], stmt.line_file()))),
        }
    }
}
