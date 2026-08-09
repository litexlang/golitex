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
        let choice_verification = self.object_choice_verification_result(stmt, checks.len())?;
        let mut success = NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, checks);
        success.object_choice_verification = Some(choice_verification);
        Ok(success.into())
    }

    /// Mathematical contract: an object introduction is meaningful when each
    /// declared parameter type is meaningful in dependency order; nonemptiness
    /// of object carriers is proved in the following verification phase.
    fn exec_have_obj_in_nonempty_set_or_param_type_stmt_verify_well_definedness(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<(), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.define_params_with_type(&stmt.param_def, false, ParamObjType::Identifier)
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
            rt.define_params_with_type(&stmt.param_def, false, ParamObjType::Identifier)
                .map_err(|define_params_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
                })?;
            rt.object_introduction_nonempty_checks_for_param_def(&stmt.param_def)
                .map_err(|check_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), check_error)
                })
        })
    }

    pub(crate) fn exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = if self.current_execution_is_trusted_file() {
            self.define_params_with_type_trusted(&stmt.param_def, ParamObjType::Identifier)
        } else {
            self.define_params_with_type(&stmt.param_def, false, ParamObjType::Identifier)
        }
        .map_err(|define_params_error| {
            exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), define_params_error)
        })?;
        infer_result.relabel_all_added_facts_with_store_reason(
            HaveObjInNonemptySetOrParamTypeStmt::store_reason(),
        );
        Ok(infer_result)
    }

    pub(crate) fn exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment_only(
        &mut self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result =
            self.exec_have_obj_in_nonempty_set_or_param_type_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    fn object_choice_verification_result(
        &self,
        stmt: &HaveObjInNonemptySetOrParamTypeStmt,
        check_count: usize,
    ) -> Result<ObjectChoiceVerificationResult, RuntimeError> {
        let items = self.object_introduction_items_for_defined_params(
            &stmt.param_def,
            stmt.line_file.clone(),
            ParamObjType::Identifier,
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

        let mut next_check_index = 0;
        let mut nonempty_check_indices = Vec::with_capacity(selected_type_facts.len());
        for group in stmt.param_def.groups.iter() {
            let check_index = if matches!(group.param_type, ParamType::Obj(_)) {
                let index = next_check_index;
                next_check_index += 1;
                Some(index)
            } else {
                None
            };
            for _ in group.params.iter() {
                nonempty_check_indices.push(check_index);
            }
        }
        if next_check_index != check_count
            || nonempty_check_indices.len() != selected_type_facts.len()
        {
            return Err(exec_stmt_error_with_stmt_and_cause(
                stmt.clone().into(),
                RuntimeError::from(UnknownRuntimeError(RuntimeErrorStruct::new_with_just_msg(
                    "object choice verification has inconsistent type-check evidence".to_string(),
                ))),
            ));
        }

        Ok(ObjectChoiceVerificationResult::new(
            selected_type_facts,
            nonempty_check_indices,
        ))
    }
}
