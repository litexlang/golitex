use crate::prelude::*;

impl Runtime {
    pub fn exec_def_prop_stmt(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let run_in_local_env = self
            .exec_def_prop_stmt_verify_well_definedness(def_prop_stmt)
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(def_prop_stmt.clone().into(), e))?;
        self.exec_def_prop_stmt_verify_process(def_prop_stmt)?;
        let infer_result = self.exec_def_prop_stmt_affect_environment(def_prop_stmt)?;
        Ok(
            SuccessDefinitionStmtResult::DefPropStmt(Box::new(SuccessDefPropStmtResult {
                statement: def_prop_stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                run_in_local_env: Some(run_in_local_env),
            }))
            .into(),
        )
    }

    /// Mathematical contract: a concrete proposition definition is checked in
    /// a fresh local scope containing its typed formal parameters.
    fn exec_def_prop_stmt_verify_well_definedness(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<SuccessVerifyDefPropLocalEnvResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.exec_def_prop_stmt_verify_well_definedness_body(def_prop_stmt)
        })
    }

    /// Mathematical contract: every parameter type is meaningful in
    /// dependency order and every defining iff-fact is meaningful under those
    /// parameters and preceding local definition facts.
    fn exec_def_prop_stmt_verify_well_definedness_body(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<SuccessVerifyDefPropLocalEnvResult, RuntimeError> {
        let verify_state = VerifyState::initial();
        let binder = self
            .verify_fact_binder_result(
                &def_prop_stmt.typed_parameters,
                BindingScope::LocalBinder,
                &verify_state,
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(def_prop_stmt.clone().into(), e))?;

        let mut body = Vec::with_capacity(def_prop_stmt.iff_facts.len());
        for fact in def_prop_stmt.iff_facts.iter() {
            body.push(
                self.verify_and_store_fact_wd_result(fact, &verify_state)
                    .map_err(|inner_exec_error| {
                        exec_stmt_error_with_stmt_and_cause(
                            def_prop_stmt.clone().into(),
                            inner_exec_error,
                        )
                    })?,
            );
        }
        Ok(SuccessVerifyDefPropLocalEnvResult { binder, body })
    }

    fn exec_def_prop_stmt_verify_process(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<(), RuntimeError> {
        let name = def_prop_stmt.name.clone();
        let env = self.top_level_env();
        if env.definitions.predicate_definitions.contains_key(&name) {
            return Err(def_prop_name_already_used_error(&name, "prop"));
        }
        if env
            .definitions
            .abstract_predicate_definitions
            .contains_key(&name)
        {
            return Err(def_prop_name_already_used_error(&name, "abstract_prop"));
        }
        Ok(())
    }

    pub fn exec_def_prop_stmt_affect_environment(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        self.store_def_prop(def_prop_stmt)?;
        Ok(SuccessInferResult::new())
    }

    pub fn exec_def_prop_stmt_affect_environment_only(
        &mut self,
        def_prop_stmt: &DefPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_def_prop_stmt_affect_environment(def_prop_stmt)?;
        Ok(
            SuccessDefinitionStmtResult::DefPropStmt(Box::new(SuccessDefPropStmtResult {
                statement: def_prop_stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                run_in_local_env: None,
            }))
            .into(),
        )
    }
}

fn def_prop_name_already_used_error(name: &str, existing_namespace: &str) -> RuntimeError {
    NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
        "name `{}` is already used in this scope as {}",
        name, existing_namespace
    )))
    .into()
}
