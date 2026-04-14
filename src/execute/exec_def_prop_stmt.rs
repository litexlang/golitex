use crate::prelude::*;

impl Runtime {
    pub fn exec_def_prop_stmt(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| rt.def_prop_stmt_check_well_defined(def_prop_stmt))
            .map_err(|e| {
                let __stmt: Stmt = def_prop_stmt.clone().into();
                let __line_file = __stmt.line_file();
                RuntimeErrorStruct::new(Some(__stmt), "".to_string(), __line_file, Some(e), vec![])
            })?;
        self.store_def_prop(def_prop_stmt)?;
        Ok(
            (NonFactualStmtSuccess::new(def_prop_stmt.clone().into(), InferResult::new(), vec![]))
                .into(),
        )
    }

    fn def_prop_stmt_check_well_defined(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<(), RuntimeError> {
        self.define_params_with_type(&def_prop_stmt.params_def_with_type, false)
            .map_err(|e| {
                let __stmt: Stmt = def_prop_stmt.clone().into();
                let __line_file = __stmt.line_file();
                RuntimeErrorStruct::new(Some(__stmt), "".to_string(), __line_file, Some(e), vec![])
            })?;

        for fact in def_prop_stmt.iff_facts.iter() {
            self.verify_fact_well_defined_and_store_and_infer(
                fact.clone(),
                &VerifyState::new(0, false),
            )
            .map_err(|inner_exec_error| {
                let __stmt: Stmt = def_prop_stmt.clone().into();
                let __line_file = __stmt.line_file();
                RuntimeErrorStruct::new(
                    Some(__stmt),
                    "".to_string(),
                    __line_file,
                    Some(inner_exec_error),
                    vec![],
                )
            })?;
        }
        Ok(())
    }
}
