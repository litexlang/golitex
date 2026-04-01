use crate::prelude::*;

impl Runtime {
    pub fn def_param_type_struct_stmt(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let struct_definition_infer_result =
            self.def_param_type_struct_stmt_check_well_defined(def_param_type_struct_stmt)?;

        self.store_def_param_type_struct(def_param_type_struct_stmt)
            .map_err(|store_error| {
                ExecStmtError::new(
                    Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                    "".to_string(),
                    Some(store_error.into()),
                    vec![],
                )
            })?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                struct_definition_infer_result,
                vec![],
            ),
        ))
    }

    fn def_param_type_struct_stmt_check_well_defined(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<InferResult, ExecStmtError> {
        self.push_env();
        let struct_check_well_defined_result = self
            .def_param_type_struct_stmt_check_well_defined_body(def_param_type_struct_stmt);
        self.pop_env();
        struct_check_well_defined_result
    }

    fn def_param_type_struct_stmt_check_well_defined_body(
        &mut self,
        _def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<InferResult, ExecStmtError> {
        unimplemented!()
    }
}
