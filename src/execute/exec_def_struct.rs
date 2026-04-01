use crate::prelude::*;

impl Runtime {
    pub fn def_struct_with_fields_stmt(
        &mut self,
        def_struct_with_fields_stmt: &DefStructWithFieldsStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let struct_definition_infer_result =
            self.def_struct_with_fields_stmt_check_well_defined(def_struct_with_fields_stmt)?;

        self.store_def_struct_with_fields(def_struct_with_fields_stmt)
            .map_err(|store_error| {
                ExecStmtError::new(
                    Stmt::DefStructWithFieldsStmt(def_struct_with_fields_stmt.clone()),
                    "".to_string(),
                    Some(store_error.into()),
                    vec![],
                )
            })?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefStructWithFieldsStmt(def_struct_with_fields_stmt.clone()),
                struct_definition_infer_result,
                vec![],
            ),
        ))
    }

    fn def_struct_with_fields_stmt_check_well_defined(
        &mut self,
        def_struct_with_fields_stmt: &DefStructWithFieldsStmt,
    ) -> Result<InferResult, ExecStmtError> {
        self.push_env();
        let struct_check_well_defined_result =
            self.def_struct_with_fields_stmt_check_well_defined_body(def_struct_with_fields_stmt);
        self.pop_env();
        struct_check_well_defined_result
    }

    fn def_struct_with_fields_stmt_check_well_defined_body(
        &mut self,
        _def_struct_with_fields_stmt: &DefStructWithFieldsStmt,
    ) -> Result<InferResult, ExecStmtError> {
        unimplemented!()
    }
}
