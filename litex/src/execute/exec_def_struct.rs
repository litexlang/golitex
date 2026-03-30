use crate::prelude::*;

impl Runtime {
    pub fn def_struct_with_no_field_stmt(
        &mut self,
        def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        return Err(ExecStmtError::new(
            Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone()),
            "not implemented".to_string(),
            None,
            vec![],
        ));
    }

    pub fn def_struct_with_fields_stmt(
        &mut self,
        def_struct_with_fields_stmt: &DefStructWithFieldsStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        return Err(ExecStmtError::new(
            Stmt::DefStructWithFieldsStmt(def_struct_with_fields_stmt.clone()),
            "not implemented".to_string(),
            None,
            vec![],
        ));
    }
}
