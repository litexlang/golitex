use crate::prelude::*;

impl Runtime {
    pub fn exec_have_exist_obj_stmt(
        &mut self,
        have_exist_obj_stmt: &HaveByExistStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_exist_obj_core(
            have_exist_obj_stmt.clone().into(),
            &have_exist_obj_stmt.equal_tos,
            &have_exist_obj_stmt.equal_to_bindings,
            &have_exist_obj_stmt.exist_fact_in_have_obj_st,
            have_exist_obj_stmt.line_file.clone(),
        )
    }

    pub(crate) fn exec_have_exist_obj_stmt_affect_environment_only(
        &mut self,
        have_exist_obj_stmt: &HaveByExistStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_have_exist_obj_stmt_affect_environment(
            have_exist_obj_stmt.clone().into(),
            &have_exist_obj_stmt.equal_to_bindings,
            &have_exist_obj_stmt.exist_fact_in_have_obj_st,
            have_exist_obj_stmt.line_file.clone(),
        )?;
        Ok(
            NonFactualStmtSuccess::new(have_exist_obj_stmt.clone().into(), infer_result, vec![])
                .into(),
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
        let equal_to_bindings = stmt.param_def.collect_param_bindings();
        self.exec_have_exist_obj_core(
            stmt.clone().into(),
            &equal_tos,
            &equal_to_bindings,
            &exist_fact,
            stmt.line_file.clone(),
        )
    }

    pub(crate) fn exec_have_obj_by_exist_facts_stmt_affect_environment_only(
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
        let equal_to_bindings = stmt.param_def.collect_param_bindings();
        let infer_result = self.exec_have_exist_obj_stmt_affect_environment(
            stmt.clone().into(),
            &equal_to_bindings,
            &exist_fact,
            stmt.line_file.clone(),
        )?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    fn exec_have_exist_obj_core(
        &mut self,
        stmt: Stmt,
        equal_tos: &[String],
        equal_to_bindings: &[SymbolBinding],
        exist_fact_in_have_obj_stmt: &ExistFactEnum,
        line_file: LineFile,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_exist_obj_stmt_verify_well_definedness(
            stmt.clone(),
            equal_tos,
            equal_to_bindings,
            exist_fact_in_have_obj_stmt,
        )?;
        let inside_results = self
            .exec_have_exist_obj_stmt_verify_process(stmt.clone(), exist_fact_in_have_obj_stmt)?;
        let infer_result = self.exec_have_exist_obj_stmt_affect_environment(
            stmt.clone(),
            equal_to_bindings,
            exist_fact_in_have_obj_stmt,
            line_file,
        )?;

        Ok((NonFactualStmtSuccess::new(stmt, infer_result, inside_results)).into())
    }

    fn exec_have_exist_obj_stmt_verify_well_definedness(
        &mut self,
        stmt: Stmt,
        equal_tos: &[String],
        equal_to_bindings: &[SymbolBinding],
        exist_fact_in_have_obj_stmt: &ExistFactEnum,
    ) -> Result<(), RuntimeError> {
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

        self.run_in_local_env(|rt| {
            rt.verify_exist_fact_well_defined(
                exist_fact_in_have_obj_stmt,
                &VerifyState::new(0, false),
            )
            .map_err(|well_defined_error| {
                exec_stmt_error_with_stmt_and_cause(stmt.clone(), well_defined_error)
            })?;
            for binding in equal_to_bindings {
                rt.store_parameter_binding(binding, ParamObjType::Identifier)
                    .map_err(|e| exec_stmt_error_with_stmt_and_cause(stmt.clone(), e))?;
            }
            Ok(())
        })
    }

    fn exec_have_exist_obj_stmt_verify_process(
        &mut self,
        stmt: Stmt,
        exist_fact_in_have_obj_stmt: &ExistFactEnum,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
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

        Ok(vec![result])
    }

    fn exec_have_exist_obj_stmt_affect_environment(
        &mut self,
        stmt: Stmt,
        equal_to_bindings: &[SymbolBinding],
        exist_fact_in_have_obj_stmt: &ExistFactEnum,
        line_file: LineFile,
    ) -> Result<InferResult, RuntimeError> {
        for binding in equal_to_bindings {
            self.store_parameter_binding(binding, ParamObjType::Identifier)?;
        }

        let new_obj_names_as_identifier_objs: Vec<Obj> = equal_to_bindings
            .iter()
            .map(|binding| {
                Identifier::new_bound(binding.name().to_string(), binding.as_ref()).into()
            })
            .collect();

        let mut infer_result = self
            .store_args_satisfy_param_type_when_not_defining_new_identifiers_with_reason(
                exist_fact_in_have_obj_stmt.params_def_with_type(),
                &new_obj_names_as_identifier_objs,
                line_file.clone(),
                ParamObjType::Exist,
                InferReason::ExistElimination,
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
                .verify_well_defined_and_store_and_infer_with_reason(
                    instantiated_fact,
                    &body_fact_verify_state,
                    InferReason::ExistElimination,
                )
                .map_err(|store_fact_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), store_fact_error)
                })?;
            infer_result.new_infer_result_inside(fact_infer_result);
        }

        if exist_fact_in_have_obj_stmt.is_exist_unique() {
            let uniqueness_forall = self
                .build_exist_unique_uniqueness_forall_fact(exist_fact_in_have_obj_stmt)
                .map_err(|runtime_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), runtime_error)
                })?;
            let uniqueness_infer_result = self
                .store_fact_without_forall_coverage_check_and_infer(uniqueness_forall.into())
                .map_err(|store_fact_error| {
                    exec_stmt_error_with_stmt_and_cause(stmt.clone(), store_fact_error)
                })?;
            infer_result.new_infer_result_inside(uniqueness_infer_result);
        }

        Ok(infer_result)
    }
}
