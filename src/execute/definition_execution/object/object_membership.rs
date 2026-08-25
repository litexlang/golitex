use crate::prelude::*;

impl Runtime {
    pub fn exec_have_obj_in_nonempty_set_or_param_type_stmt(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_obj_in_nonempty_set_or_param_type_stmt_verify_well_definedness(stmt)?;
        let checks = self.exec_have_obj_in_nonempty_set_or_param_type_stmt_verify_process(stmt)?;
        let infer_result =
            self.exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment(stmt)?;
        let choice_verification = self.object_choice_verification_result(stmt, checks)?;
        Ok(
            SuccessDefinitionStmtResult::HaveObjInNonemptySetStmt(Box::new(
                SuccessHaveObjInNonemptySetStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: Some(choice_verification),
                },
            ))
            .into(),
        )
    }

    /// Mathematical contract: an object definition is meaningful when each
    /// defined parameter type is meaningful in dependency order; nonemptiness
    /// of object carriers is proved in the following verification phase.
    fn exec_have_obj_in_nonempty_set_or_param_type_stmt_verify_well_definedness(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.define_params_with_type(&stmt.param_def, false, BindingScope::DefinitionBinding)
                .map_err(|define_params_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
                })?;
            Ok(())
        })
    }

    fn exec_have_obj_in_nonempty_set_or_param_type_stmt_verify_process(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.define_params_with_type(&stmt.param_def, false, BindingScope::DefinitionBinding)
                .map_err(|define_params_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
                })?;
            rt.object_definition_nonempty_checks_for_param_def(&stmt.param_def)
                .map_err(|check_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), check_error)
                })
        })
    }

    pub fn exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut infer_result = if self.current_execution_is_trusted_file() {
            self.define_params_with_type_trusted(&stmt.param_def, BindingScope::DefinitionBinding)
        } else {
            self.define_params_with_type(&stmt.param_def, false, BindingScope::DefinitionBinding)
        }
        .map_err(|define_params_error| {
            exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
        })?;
        infer_result.relabel_all_added_facts_with_store_reason(
            HaveObjInNonemptySetOrParamTypeStmt::store_reason(),
        );
        Ok(infer_result)
    }

    pub fn exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment_only(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result =
            self.exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment(stmt)?;
        Ok(
            SuccessDefinitionStmtResult::HaveObjInNonemptySetStmt(Box::new(
                SuccessHaveObjInNonemptySetStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: None,
                },
            ))
            .into(),
        )
    }

    fn object_choice_verification_result(
        &self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
        checks: Vec<StmtResult>,
    ) -> Result<SuccessVerifyObjectChoiceResult, RuntimeError> {
        let items = self.object_definition_items_for_defined_params(
            &stmt.param_def,
            stmt.line_file.clone(),
            BindingScope::DefinitionBinding,
        );
        let mut selected_type_facts = Vec::with_capacity(items.len());
        for item in items {
            if item.facts.len() != 1 {
                return Err(exec_stmt_error_with_stmt_and_cause(
                    stmt.clone().into(),
                    RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                        format!(
                            "object choice `{}` did not produce exactly one type fact",
                            item.name
                        ),
                    ))),
                ));
            }
            selected_type_facts.push(item.facts[0].clone());
        }

        let mut checks = checks.into_iter();
        let mut groups = Vec::with_capacity(stmt.param_def.groups.len());
        let mut selected_type_facts = selected_type_facts.into_iter();
        for group in stmt.param_def.groups.iter() {
            let nonempty_check = if matches!(group.param_type, ParamType::Obj(_)) {
                Some(Box::new(checks.next().ok_or_else(|| {
                    exec_stmt_error_with_stmt_and_cause(
                        stmt.clone().into(),
                        RuntimeError::from(UnknownRuntimeError(
                            RuntimeErrorStruct::new_with_just_msg(
                                "object choice verification is missing nonempty evidence"
                                    .to_string(),
                            ),
                        )),
                    )
                })?))
            } else {
                None
            };
            let mut group_type_facts = Vec::with_capacity(group.params.len());
            for _ in group.params.iter() {
                group_type_facts.push(
                    selected_type_facts
                        .next()
                        .expect("object choice facts must match defined parameters"),
                );
            }
            groups.push(SuccessVerifyObjectChoiceGroupResult {
                selected_type_facts: group_type_facts,
                nonempty_check,
            });
        }
        if checks.next().is_some() || selected_type_facts.next().is_some() {
            return Err(exec_stmt_error_with_stmt_and_cause(
                stmt.clone().into(),
                RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                    "object choice verification has inconsistent type-check evidence".to_string(),
                ))),
            ));
        }

        Ok(SuccessVerifyObjectChoiceResult::new(groups))
    }
}
