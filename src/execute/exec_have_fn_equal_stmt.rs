use crate::prelude::*;
impl Runtime {
    pub fn exec_have_fn_equal_stmt(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set_stored =
            self.exec_have_fn_equal_stmt_verify_well_definedness(have_fn_equal_stmt)?;
        let inside_results = self.exec_have_fn_equal_stmt_verify_process(have_fn_equal_stmt)?;
        let infer_result =
            self.exec_have_fn_equal_stmt_affect_environment(have_fn_equal_stmt, &fn_set_stored)?;

        Ok((NonFactualStmtSuccess::new(
            have_fn_equal_stmt.clone().into(),
            infer_result,
            inside_results,
        ))
        .into())
    }

    fn store_have_fn_equal_stmt_facts(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<InferResult, RuntimeError> {
        self.store_free_param_or_identifier_name(
            &have_fn_equal_stmt.name,
            ParamObjType::Identifier,
        )?;

        let function_identifier_obj = self.declared_identifier_obj(&have_fn_equal_stmt.name);
        let function_set_obj = fn_set_stored.clone().into();
        let function_in_function_set_fact = InFact::new(
            function_identifier_obj.clone(),
            function_set_obj,
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();

        let infer_result = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state_and_reason(
                function_in_function_set_fact,
                InferReason::FunctionDefinition,
            )
            .map_err(|store_fact_error| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "",
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        let stmt_lf = have_fn_equal_stmt.line_file.clone();
        self.register_known_objs_in_fn_sets_for_element_body(
            &function_identifier_obj,
            fn_set_stored.body.clone(),
            Some((*have_fn_equal_stmt.equal_to_anonymous_fn.equal_to).clone()),
            stmt_lf.clone(),
            stmt_lf,
        );

        let function_equals_anonymous_fn_fact: AtomicFact = EqualFact::new(
            function_identifier_obj,
            have_fn_equal_stmt.equal_to_anonymous_fn.clone().into(),
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();
        let function_definition_infer_result = self
            .store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                function_equals_anonymous_fn_fact,
                HaveFnEqualStmt::store_reason(),
            )
            .map_err(|store_fact_error| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "",
                    Some(store_fact_error),
                    vec![],
                )
            })?;
        let mut infer_result = infer_result;
        infer_result.new_infer_result_inside(function_definition_infer_result);

        Ok(infer_result)
    }

    pub(crate) fn exec_have_fn_equal_stmt_affect_environment_only(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set_stored = FnSet::from_body(have_fn_equal_stmt.equal_to_anonymous_fn.body.clone())
            .map_err(|e| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "have_fn_equal_stmt: build fn set for storage failed".to_string(),
                    Some(e),
                    vec![],
                )
            })?;
        let infer_result =
            self.exec_have_fn_equal_stmt_affect_environment(have_fn_equal_stmt, &fn_set_stored)?;
        Ok(
            NonFactualStmtSuccess::new(have_fn_equal_stmt.clone().into(), infer_result, vec![])
                .into(),
        )
    }

    fn exec_have_fn_equal_stmt_verify_well_definedness(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<FnSet, RuntimeError> {
        let fn_set_stored = FnSet::from_body(have_fn_equal_stmt.equal_to_anonymous_fn.body.clone())
            .map_err(|e| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "have_fn_equal_stmt: build fn set for storage failed".to_string(),
                    Some(e),
                    vec![],
                )
            })?;

        self.run_in_local_env(|rt| {
            rt.have_fn_equal_stmt_verify_well_defined_body(have_fn_equal_stmt, &fn_set_stored)
        })
        .map_err(|e| {
            short_exec_error(
                have_fn_equal_stmt.clone().into(),
                "have_fn_equal_stmt: verify well-defined failed".to_string(),
                Some(e),
                vec![],
            )
        })?;

        Ok(fn_set_stored)
    }

    fn have_fn_equal_stmt_verify_well_defined_body(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeError> {
        let verify_state = VerifyState::new(0, false);

        self.verify_obj_well_defined_and_store_cache(
            &have_fn_equal_stmt.equal_to_anonymous_fn.clone().into(),
            &verify_state,
        )
        .map_err(|well_defined_error| {
            short_exec_error(
                have_fn_equal_stmt.clone().into(),
                "",
                Some(well_defined_error),
                vec![],
            )
        })?;

        let function_set_obj = fn_set_stored.clone().into();
        self.verify_obj_well_defined_and_store_cache(&function_set_obj, &verify_state)
            .map_err(|well_defined_error| {
                short_exec_error(
                    have_fn_equal_stmt.clone().into(),
                    "",
                    Some(well_defined_error),
                    vec![],
                )
            })?;
        Ok(())
    }

    fn exec_have_fn_equal_stmt_verify_process(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let verify_result =
            self.have_fn_equal_stmt_verify_return_value_in_ret_set(have_fn_equal_stmt)?;
        if verify_result.is_unknown() {
            let msg = format!(
                "have_fn_equal_stmt: {} is not in return set {}",
                have_fn_equal_stmt.equal_to_anonymous_fn.equal_to,
                have_fn_equal_stmt.equal_to_anonymous_fn.body.ret_set
            );
            return Err(short_exec_error(
                have_fn_equal_stmt.clone().into(),
                msg,
                None,
                vec![],
            ));
        }
        Ok(vec![verify_result])
    }

    fn exec_have_fn_equal_stmt_affect_environment(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<InferResult, RuntimeError> {
        self.store_have_fn_equal_stmt_facts(have_fn_equal_stmt, fn_set_stored)
    }

    fn have_fn_equal_stmt_verify_return_value_in_ret_set(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            for param_def_with_set in have_fn_equal_stmt
                .equal_to_anonymous_fn
                .body
                .params_def_with_set
                .iter()
            {
                rt.define_params_with_set(param_def_with_set)?;
            }
            for dom_fact in have_fn_equal_stmt
                .equal_to_anonymous_fn
                .body
                .dom_facts
                .iter()
            {
                let _ = rt.store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    dom_fact.clone(),
                )?;
            }
            let equal_to_in_ret_set_atomic_fact = InFact::new(
                (*have_fn_equal_stmt.equal_to_anonymous_fn.equal_to).clone(),
                (*have_fn_equal_stmt.equal_to_anonymous_fn.body.ret_set).clone(),
                have_fn_equal_stmt.line_file.clone(),
            )
            .into();
            let result = rt.verify_atomic_fact(
                &equal_to_in_ret_set_atomic_fact,
                &VerifyState::new(0, false),
            )?;
            if !result.is_unknown() {
                return Ok(result);
            }

            if let Some(result) = rt.verify_anonymous_fn_in_declared_return_set_by_definition(
                have_fn_equal_stmt,
                &VerifyState::new(0, false),
            )? {
                return Ok(result);
            }

            Ok(result)
        })
        .map_err(|verify_error| {
            short_exec_error(
                have_fn_equal_stmt.clone().into(),
                "",
                Some(verify_error),
                vec![],
            )
        })
    }

    fn verify_anonymous_fn_in_declared_return_set_by_definition(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        verify_state: &VerifyState,
    ) -> Result<Option<StmtResult>, RuntimeError> {
        let Obj::AnonymousFn(value_fn) = have_fn_equal_stmt
            .equal_to_anonymous_fn
            .equal_to
            .as_ref()
            .clone()
        else {
            return Ok(None);
        };

        let declared_return_set = have_fn_equal_stmt
            .equal_to_anonymous_fn
            .body
            .ret_set
            .as_ref()
            .clone();
        let mut return_set_representatives = vec![declared_return_set.clone()];
        return_set_representatives
            .extend(self.get_all_obj_representatives_equal_to_given(&declared_return_set));
        for return_set_representative in return_set_representatives {
            let Obj::SetBuilder(_) = return_set_representative else {
                continue;
            };
            let representative_membership: AtomicFact = InFact::new(
                value_fn.clone().into(),
                return_set_representative,
                have_fn_equal_stmt.line_file.clone(),
            )
            .into();
            let representative_result =
                self.verify_atomic_fact(&representative_membership, verify_state)?;
            if !representative_result.is_true() {
                continue;
            }
            let membership_fact: Fact = InFact::new(
                value_fn.clone().into(),
                declared_return_set,
                have_fn_equal_stmt.line_file.clone(),
            )
            .into();
            return Ok(Some(
                FactualStmtSuccess::new_with_verified_by_builtin_rules_recording_stmt(
                    membership_fact,
                    "anonymous fn satisfies a declared set-builder return set".to_string(),
                    vec![representative_result],
                )
                .into(),
            ));
        }

        Ok(None)
    }
}
