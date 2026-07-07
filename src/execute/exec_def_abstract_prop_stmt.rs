use crate::prelude::*;

impl Runtime {
    pub fn exec_def_abstract_prop_stmt(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_def_abstract_prop_stmt_verify_well_definedness(def_abstract_prop_stmt)
            .map_err(|e| {
                exec_stmt_error_with_stmt_and_cause(def_abstract_prop_stmt.clone().into(), e)
            })?;
        let inside_results = self
            .exec_def_abstract_prop_stmt_verify_process(def_abstract_prop_stmt)
            .map_err(|e| {
                exec_stmt_error_with_stmt_and_cause(def_abstract_prop_stmt.clone().into(), e)
            })?;
        let infer_result = self
            .exec_def_abstract_prop_stmt_affect_environment(def_abstract_prop_stmt)
            .map_err(|e| {
                exec_stmt_error_with_stmt_and_cause(def_abstract_prop_stmt.clone().into(), e)
            })?;
        Ok(NonFactualStmtSuccess::new(
            def_abstract_prop_stmt.clone().into(),
            infer_result,
            inside_results,
        )
        .into())
    }

    fn exec_def_abstract_prop_stmt_verify_well_definedness(
        &mut self,
        _def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<(), RuntimeError> {
        Ok(())
    }

    fn exec_def_abstract_prop_stmt_verify_process(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let name = def_abstract_prop_stmt.name.clone();
        let env = self.top_level_env();
        if env.defined_abstract_props.contains_key(&name) {
            return Err(def_abstract_prop_name_already_used_error(
                &name,
                "abstract_prop",
            ));
        }
        if env.defined_def_props.contains_key(&name) {
            return Err(def_abstract_prop_name_already_used_error(&name, "prop"));
        }
        Ok(vec![])
    }

    pub(crate) fn exec_def_abstract_prop_stmt_affect_environment(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<InferResult, RuntimeError> {
        self.store_def_abstract_prop(def_abstract_prop_stmt)?;
        Ok(InferResult::new())
    }

    pub(crate) fn exec_def_abstract_prop_stmt_affect_environment_only(
        &mut self,
        def_abstract_prop_stmt: &DefAbstractPropStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result =
            self.exec_def_abstract_prop_stmt_affect_environment(def_abstract_prop_stmt)?;
        Ok(
            NonFactualStmtSuccess::new(def_abstract_prop_stmt.clone().into(), infer_result, vec![])
                .into(),
        )
    }
}

fn def_abstract_prop_name_already_used_error(name: &str, existing_namespace: &str) -> RuntimeError {
    NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new_with_just_msg(format!(
        "name `{}` is already used in this scope as {}",
        name, existing_namespace
    )))
    .into()
}
