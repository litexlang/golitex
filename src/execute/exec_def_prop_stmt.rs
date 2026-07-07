use crate::prelude::*;

impl Runtime {
    pub fn exec_def_prop_stmt(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_def_prop_stmt_verify_well_definedness(def_prop_stmt)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(def_prop_stmt.clone().into(), e))?;
        let inside_results = self.exec_def_prop_stmt_verify_process(def_prop_stmt)?;
        let infer_result = self.exec_def_prop_stmt_affect_environment(def_prop_stmt)?;
        Ok(
            NonFactualStmtSuccess::new(def_prop_stmt.clone().into(), infer_result, inside_results)
                .into(),
        )
    }

    fn exec_def_prop_stmt_verify_well_definedness(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.exec_def_prop_stmt_verify_well_definedness_body(def_prop_stmt)
        })
    }

    fn exec_def_prop_stmt_verify_well_definedness_body(
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

    fn exec_def_prop_stmt_verify_process(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let name = def_prop_stmt.name.clone();
        let env = self.top_level_env();
        if env.defined_def_props.contains_key(&name) {
            return Err(def_prop_name_already_used_error(&name, "prop"));
        }
        if env.defined_abstract_props.contains_key(&name) {
            return Err(def_prop_name_already_used_error(&name, "abstract_prop"));
        }
        Ok(vec![])
    }

    pub(crate) fn exec_def_prop_stmt_affect_environment(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<InferResult, RuntimeError> {
        self.store_def_prop(def_prop_stmt)?;
        Ok(InferResult::new())
    }

    pub(crate) fn exec_def_prop_stmt_affect_environment_only(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_def_prop_stmt_affect_environment(def_prop_stmt)?;
        Ok(NonFactualStmtSuccess::new(def_prop_stmt.clone().into(), infer_result, vec![]).into())
    }
}

fn def_prop_name_already_used_error(name: &str, existing_namespace: &str) -> RuntimeError {
    NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
        "name `{}` is already used in this scope as {}",
        name, existing_namespace
    )))
    .into()
}
