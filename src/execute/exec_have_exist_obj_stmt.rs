use crate::prelude::*;

impl Runtime {
    pub fn exec_have_exist_obj_stmt(
        &mut self,
        have_exist_obj_stmt: &HaveByExistStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_exist_obj_core(
            have_exist_obj_stmt.clone().into(),
            &have_exist_obj_stmt.equal_tos,
            &have_exist_obj_stmt.exist_fact_in_have_obj_st,
            have_exist_obj_stmt.line_file.clone(),
        )
    }

    pub fn exec_have_obj_by_exist_facts_stmt(
        &mut self,
        stmt: &HaveObjByExistFactsStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let body = ExistFactBody::new(
            stmt.param_def.clone(),
            stmt.facts.clone(),
            stmt.line_file.clone(),
        )
        .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), e))?;
        let exist_fact = ExistFactEnum::ExistFact(body);
        let equal_tos = stmt.param_def.collect_param_names();
        self.exec_have_exist_obj_core(
            stmt.clone().into(),
            &equal_tos,
            &exist_fact,
            stmt.line_file.clone(),
        )
    }

    fn exec_have_exist_obj_core(
        &mut self,
        stmt: Stmt,
        equal_tos: &[String],
        exist_fact_in_have_obj_stmt: &ExistFactEnum,
        line_file: LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        let verify_state = VerifyState::new(0, false);

        let result = self
            .verify_exist_fact(exist_fact_in_have_obj_stmt, &verify_state)
            .map_err(|verify_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone(), verify_error)
            })?;
        if result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone(),
                "have_exist_obj_stmt: exist fact is not verified".to_string(),
                None,
                vec![],
            ));
        }

        if exist_fact_in_have_obj_stmt
            .params_def_with_type()
            .number_of_params()
            != equal_tos.len()
        {
            return Err(short_exec_error(
                stmt.clone(),
                "have_exist_obj_stmt: number of params in exist does not match number of given objs"
                    .to_string(),
                None,
                vec![],
            ));
        }

        for obj in equal_tos.iter() {
            self.store_free_param_or_identifier_name(obj, ParamObjType::Exist)?;
        }

        let new_obj_names_as_identifier_objs = equal_tos
            .iter()
            .map(|s| Identifier::new(s.clone()).into())
            .collect();

        let mut infer_result = self
            .store_args_satisfy_param_type_when_not_defining_new_identifiers(
                exist_fact_in_have_obj_stmt.params_def_with_type(),
                &new_obj_names_as_identifier_objs,
                line_file,
                ParamObjType::Exist,
            )
            .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;

        let param_to_obj_map = exist_fact_in_have_obj_stmt
            .params_def_with_type()
            .param_defs_and_args_to_param_to_arg_map(new_obj_names_as_identifier_objs.as_slice());

        let body_fact_verify_state = VerifyState::new(0, false);
        for fact in exist_fact_in_have_obj_stmt.facts().iter() {
            let instantiated_fact = self
                .inst_exist_body_fact(fact, &param_to_obj_map, ParamObjType::Exist, None)
                .map_err(|runtime_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), runtime_error)
                })?
                .to_fact();
            let fact_infer_result = self
                .verify_well_defined_and_store_and_infer(instantiated_fact, &body_fact_verify_state)
                .map_err(|store_fact_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), store_fact_error)
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }

        Ok((NonFactualStmtSuccess::new(stmt, infer_result, vec![result])).into())
    }
}
