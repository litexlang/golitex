use crate::prelude::*;

impl Runtime {
    pub fn exec_def_prop_stmt(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| rt.def_prop_stmt_check_well_defined(def_prop_stmt))
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(def_prop_stmt.clone().into(), e))?;
        self.store_def_prop(def_prop_stmt)?;
        Ok(NonFactualStmtSuccess::new_with_stmt(def_prop_stmt.clone().into()).into())
    }

    fn def_prop_stmt_check_well_defined(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<(), RuntimeError> {
        self.define_params_with_type(
            &def_prop_stmt.params_def_with_type,
            false,
            ParamObjType::DefHeader,
        )
        .map_err(|e| exec_stmt_error_with_stmt_and_cause(def_prop_stmt.clone().into(), e))?;

        for fact in def_prop_stmt.iff_facts.iter() {
            self.verify_fact_well_defined_and_store_and_infer(
                fact.clone(),
                &VerifyState::new(0, false),
            )
            .map_err(|inner_exec_error| {
                exec_stmt_error_with_stmt_and_cause(def_prop_stmt.clone().into(), inner_exec_error)
            })?;
        }
        Ok(())
    }
}
