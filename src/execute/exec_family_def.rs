use crate::prelude::*;

impl Runtime {
    pub fn def_family_stmt(
        &mut self,
        def_family_stmt: &DefFamilyStmt,
    ) -> Result<NonErrStmtExecResult, ExecStmtError> {
        let family_definition_infer_result =
            self.def_family_stmt_check_well_defined(def_family_stmt)?;

        self.store_def_family(def_family_stmt)
            .map_err(|store_error| {
                ExecStmtError::new(
                    Stmt::DefFamilyStmt(def_family_stmt.clone()),
                    "failed to store family definition".to_string(),
                    Some(store_error.into()),
                    vec![],
                )
            })?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::DefFamilyStmt(def_family_stmt.clone()),
                family_definition_infer_result,
                vec![],
            ),
        ))
    }

    fn def_family_stmt_check_well_defined(
        &mut self,
        def_family_stmt: &DefFamilyStmt,
    ) -> Result<InferResult, ExecStmtError> {
        self.push_env();
        let family_check_well_defined_result =
            self.def_family_stmt_check_well_defined_body(def_family_stmt);
        self.pop_env();
        family_check_well_defined_result
    }

    fn def_family_stmt_check_well_defined_body(
        &mut self,
        def_family_stmt: &DefFamilyStmt,
    ) -> Result<InferResult, ExecStmtError> {
        let verify_state = VerifyState::new(0, false);
        let mut family_definition_infer_result = self
            .define_params_with_type(&def_family_stmt.params_def_with_type, false)
            .map_err(|define_params_error| {
                ExecStmtError::new(
                    Stmt::DefFamilyStmt(def_family_stmt.clone()),
                    "".to_string(),
                    Some(define_params_error.into()),
                    vec![],
                )
            })?;

        for dom_fact in def_family_stmt.dom_facts.iter() {
            let dom_fact_infer_result = self
                .verify_or_and_chain_atomic_fact_well_defined_and_store_and_infer(
                    dom_fact,
                    &verify_state,
                )
                .map_err(|inner_exec_error| {
                    ExecStmtError::new(
                        Stmt::DefFamilyStmt(def_family_stmt.clone()),
                        "".to_string(),
                        Some(RuntimeError::ExecStmtError(inner_exec_error)),
                        vec![],
                    )
                })?;
            family_definition_infer_result.new_infer_result_inside(dom_fact_infer_result);
        }

        self.verify_obj_well_defined_and_store_cache(
            &def_family_stmt.equal_to,
            &verify_state,
        )
        .map_err(|well_defined_error| {
            ExecStmtError::new(
                Stmt::DefFamilyStmt(def_family_stmt.clone()),
                "".to_string(),
                Some(well_defined_error.into()),
                vec![],
            )
        })?;

        Ok(family_definition_infer_result)
    }
}
