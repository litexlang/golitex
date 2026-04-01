use crate::prelude::*;

impl Runtime {
    pub fn def_param_type_struct_stmt(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
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

        let infer_result = InferResult::new();

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(NonFactualStmtSuccess::new(
            Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
            infer_result,
            vec![],
        )))
    }

    fn def_param_type_struct_stmt_check_well_defined(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<(), ExecStmtError> {
        self.push_env();
        let struct_check_well_defined_result = self
            .def_param_type_struct_stmt_check_well_defined_body(def_param_type_struct_stmt);
        self.pop_env();
        struct_check_well_defined_result
    }

    fn def_param_type_struct_stmt_check_well_defined_body(
        &mut self,
        def_param_type_struct_stmt: &DefParamTypeStructStmt,
    ) -> Result<(), ExecStmtError> {
        let verify_state = VerifyState::new(0, false);

        self
            .define_params_with_type(&def_param_type_struct_stmt.params_def_with_type, false)
            .map_err(|define_params_error| {
                ExecStmtError::new(
                    Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                    "".to_string(),
                    Some(define_params_error.into()),
                    vec![],
                )
            })?;

        for dom_fact in def_param_type_struct_stmt.dom_facts.iter() {
            self
                .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    dom_fact,
                    &verify_state,
                )
                .map_err(|inner_exec_error| {
                    ExecStmtError::new(
                        Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                        "".to_string(),
                        Some(RuntimeError::ExecStmtError(inner_exec_error)),
                        vec![],
                    )
                })?;
        }

        for (_, field_param_type) in def_param_type_struct_stmt.fields.iter() {
            self
                .verify_param_type_well_defined(field_param_type, &verify_state)
                .map_err(|well_defined_error| {
                    ExecStmtError::new(
                        Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                        "".to_string(),
                        Some(well_defined_error.into()),
                        vec![],
                    )
                })?;
        }

        for fact in def_param_type_struct_stmt.facts.iter() {
            self
                .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    fact,
                    &verify_state,
                )
                .map_err(|inner_exec_error| {
                    ExecStmtError::new(
                        Stmt::DefParamTypeStructStmt(def_param_type_struct_stmt.clone()),
                        "".to_string(),
                        Some(RuntimeError::ExecStmtError(inner_exec_error)),
                        vec![],
                    )
                })?;
        }

        Ok(())
    }
}
