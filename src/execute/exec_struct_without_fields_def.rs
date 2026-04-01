use crate::prelude::*;

impl Runtime {
    pub fn def_struct_with_no_field_stmt(
        &mut self,
        def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let struct_definition_infer_result =
            self.def_struct_with_no_field_stmt_check_well_defined(def_struct_with_no_field_stmt)?;

        self.store_def_struct_with_no_field(def_struct_with_no_field_stmt)
            .map_err(|store_error| {
                ExecStmtError::new(
                    Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone()),
                    "failed to store struct definition".to_string(),
                    Some(store_error.into()),
                    vec![],
                )
            })?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone()),
                struct_definition_infer_result,
                vec![],
            ),
        ))
    }

    fn def_struct_with_no_field_stmt_check_well_defined(
        &mut self,
        def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt,
    ) -> Result<InferResult, ExecStmtError> {
        self.push_env();
        let struct_check_well_defined_result = self
            .def_struct_with_no_field_stmt_check_well_defined_body(def_struct_with_no_field_stmt);
        self.pop_env();
        struct_check_well_defined_result
    }

    fn def_struct_with_no_field_stmt_check_well_defined_body(
        &mut self,
        def_struct_with_no_field_stmt: &DefStructWithNoFieldStmt,
    ) -> Result<InferResult, ExecStmtError> {
        let verify_state = VerifyState::new(0, false);
        let mut struct_definition_infer_result = self
            .define_params_with_type(&def_struct_with_no_field_stmt.params_def_with_type, false)
            .map_err(|define_params_error| {
                ExecStmtError::new(
                    Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone()),
                    "".to_string(),
                    Some(define_params_error.into()),
                    vec![],
                )
            })?;

        for dom_fact in def_struct_with_no_field_stmt.dom_facts.iter() {
            let dom_fact_infer_result = self
                .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    dom_fact,
                    &verify_state,
                )
                .map_err(|inner_exec_error| {
                    ExecStmtError::new(
                        Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone()),
                        "".to_string(),
                        Some(RuntimeError::ExecStmtError(inner_exec_error)),
                        vec![],
                    )
                })?;
            struct_definition_infer_result.new_infer_result_inside(dom_fact_infer_result);
        }

        self.verify_obj_well_defined_and_store_cache(
            &def_struct_with_no_field_stmt.equal_to,
            &verify_state,
        )
        .map_err(|well_defined_error| {
            ExecStmtError::new(
                Stmt::DefStructWithNoFieldStmt(def_struct_with_no_field_stmt.clone()),
                "".to_string(),
                Some(well_defined_error.into()),
                vec![],
            )
        })?;

        Ok(struct_definition_infer_result)
    }
}