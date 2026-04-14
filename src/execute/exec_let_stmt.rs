use crate::prelude::*;

impl Runtime {
    pub fn exec_let_stmt(&mut self, def_let_stmt: &DefLetStmt) -> Result<StmtResult, RuntimeError> {
        let mut infer_result = self
            .define_params_with_type(&def_let_stmt.param_def, false)
            .map_err(|e| {
                let __stmt: Stmt = def_let_stmt.clone().into();
                let __line_file = __stmt.line_file();
                RuntimeErrorStruct::new(Some(__stmt), "".to_string(), __line_file, Some(e), vec![])
            })?;
        for fact in def_let_stmt.facts.iter() {
            let fact_infer_result = self
                .verify_fact_well_defined_and_store_and_infer(
                    fact.clone(),
                    &VerifyState::new(0, false),
                )
                .map_err(|inner_exec_error| {
                    let __stmt: Stmt = def_let_stmt.clone().into();
                    let __line_file = __stmt.line_file();
                    RuntimeErrorStruct::new(
                        Some(__stmt),
                        "".to_string(),
                        __line_file,
                        Some(inner_exec_error),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
            // Body facts are not added by infer() for chain/and/or/exist; record them for JSON / CLI.
            infer_result.new_fact(fact);
        }
        Ok((NonFactualStmtSuccess::new(def_let_stmt.clone().into(), infer_result, vec![])).into())
    }
}
