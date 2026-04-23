use crate::prelude::*;

impl Runtime {
    pub fn exec_by_matrix_set_stmt(
        &mut self,
        stmt: &ByMatrixSetStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let stmt_exec: Stmt = stmt.clone().into();
        let verify_state = VerifyState::new(0, false);
        let left: Obj = stmt.matrix_set.clone().into();
        self.verify_obj_well_defined_and_store_cache(&left, &verify_state)
            .map_err(|e| {
                short_exec_error(
                    stmt_exec.clone(),
                    format!("by matrix: `{}` is not well-defined", left),
                    Some(e),
                    vec![],
                )
            })?;

        let fn_set = self.matrix_set_to_fn_set(&stmt.matrix_set, stmt.line_file.clone());
        let right: Obj = fn_set.into();
        self.verify_obj_well_defined_and_store_cache(&right, &verify_state)
            .map_err(|e| {
                short_exec_error(
                    stmt_exec.clone(),
                    "by matrix: expanded fn set is not well-defined".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        let equal_atomic = EqualFact::new(left, right, stmt.line_file.clone());
        let equal_fact: Fact = equal_atomic.into();
        match self.verify_well_defined_and_store_and_infer_with_default_verify_state(equal_fact.clone()) {
            Ok(mut infer_result) => {
                infer_result.new_fact(&equal_fact);
                Ok((NonFactualStmtSuccess::new(stmt_exec, infer_result, vec![])).into())
            }
            Err(store_error) => Err(short_exec_error(
                stmt_exec,
                "by matrix: failed to store definitional equality".to_string(),
                Some(store_error),
                vec![],
            )),
        }
    }
}
