use crate::prelude::*;

impl Runtime {
    pub fn exec_have_exist_obj_stmt(
        &mut self,
        have_exist_obj_stmt: &HaveByExistStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let exist_fact_in_have_obj_stmt = &have_exist_obj_stmt.exist_fact_in_have_obj_st;
        let verify_state = VerifyState::new(0, false);

        let result = self
            .verify_exist_fact(exist_fact_in_have_obj_stmt, &verify_state)
            .map_err(|verify_error| {
                RuntimeError::from({
                    let __stmt: Stmt = have_exist_obj_stmt.clone().into();
                    let __line_file = __stmt.line_file();
                    RuntimeErrorStruct::new(
                        Some(__stmt),
                        "".to_string(),
                        __line_file,
                        Some(verify_error),
                        vec![],
                    )
                })
            })?;
        if result.is_unknown() {
            return Err(RuntimeError::from({
                let __stmt: Stmt = have_exist_obj_stmt.clone().into();
                let __message = "have_exist_obj_stmt: exist fact is not verified".to_string();
                let __cause = None;
                let __inside = vec![];
                let __line_file = __stmt.line_file();
                let __previous_error = if __message.is_empty() {
                    __cause
                } else {
                    Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                };
                RuntimeErrorStruct::new(
                    Some(__stmt),
                    __message,
                    __line_file,
                    __previous_error,
                    __inside,
                )
            }));
        }

        if exist_fact_in_have_obj_stmt
            .params_def_with_type
            .number_of_params()
            != have_exist_obj_stmt.equal_tos.len()
        {
            return Err(RuntimeError::from({
                let __stmt: Stmt = have_exist_obj_stmt.clone().into();
                let __message = "have_exist_obj_stmt: number of params in exist does not match number of given objs".to_string();
                let __cause = None;
                let __inside = vec![];
                let __line_file = __stmt.line_file();
                let __previous_error = if __message.is_empty() {
                    __cause
                } else {
                    Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                };
                RuntimeErrorStruct::new(
                    Some(__stmt),
                    __message,
                    __line_file,
                    __previous_error,
                    __inside,
                )
            }));
        }

        for obj in have_exist_obj_stmt.equal_tos.iter() {
            self.store_identifier_obj(obj)?;
        }

        let new_obj_names_as_identifier_objs = have_exist_obj_stmt
            .equal_tos
            .iter()
            .map(|s| s.clone().into())
            .collect();

        let mut infer_result = self
            .store_args_satisfy_param_type_when_not_defining_new_identifiers(
                &exist_fact_in_have_obj_stmt.params_def_with_type,
                &new_obj_names_as_identifier_objs,
                have_exist_obj_stmt.line_file.clone(),
            )
            .map_err(|e| {
                let __stmt: Stmt = have_exist_obj_stmt.clone().into();
                let __line_file = __stmt.line_file();
                RuntimeErrorStruct::new(Some(__stmt), "".to_string(), __line_file, Some(e), vec![])
            })?;

        let param_to_obj_map = exist_fact_in_have_obj_stmt
            .params_def_with_type
            .param_defs_and_args_to_param_to_arg_map(new_obj_names_as_identifier_objs.as_slice());

        for fact in exist_fact_in_have_obj_stmt.facts.iter() {
            let instantiated_fact = self
                .inst_or_and_chain_atomic_fact(fact, &param_to_obj_map)
                .map_err(|runtime_error| {
                    let __stmt: Stmt = have_exist_obj_stmt.clone().into();
                    let __line_file = __stmt.line_file();
                    RuntimeErrorStruct::new(
                        Some(__stmt),
                        "".to_string(),
                        __line_file,
                        Some(runtime_error),
                        vec![],
                    )
                })?
                .to_fact();
            let fact_infer_result = self
                .store_fact_without_well_defined_verified_and_infer(instantiated_fact)
                .map_err(|store_fact_error| {
                    let __stmt: Stmt = have_exist_obj_stmt.clone().into();
                    let __line_file = __stmt.line_file();
                    RuntimeErrorStruct::new(
                        Some(__stmt),
                        "".to_string(),
                        __line_file,
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }

        Ok(
            (NonFactualStmtSuccess::new(have_exist_obj_stmt.clone().into(), infer_result, vec![]))
                .into(),
        )
    }
}
