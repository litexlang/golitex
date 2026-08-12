use crate::prelude::*;
impl Runtime {
    pub fn exec_have_fn_equal_stmt(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let fn_set_stored =
            self.exec_have_fn_equal_stmt_verify_well_definedness(have_fn_equal_stmt)?;
        let (inside_results, assumption_infers) =
            self.exec_have_fn_equal_stmt_verify_process(have_fn_equal_stmt)?;
        let infer_result =
            self.exec_have_fn_equal_stmt_affect_environment(have_fn_equal_stmt, &fn_set_stored)?;

        let function_identifier_obj = self.declared_identifier_obj(have_fn_equal_stmt.name());
        let function_membership: Fact = InFact::new(
            function_identifier_obj.clone(),
            fn_set_stored.clone().into(),
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();
        let defining_equality: Fact = EqualFact::new(
            function_identifier_obj,
            have_fn_equal_stmt.equal_to_anonymous_fn.clone().into(),
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();
        let mut success = NonFactualStmtSuccess::new(
            have_fn_equal_stmt.clone().into(),
            infer_result,
            inside_results,
        );
        success.function_definition_verification = Some(FunctionDefinitionVerificationResult::new(
            0,
            assumption_infers,
            function_membership,
            defining_equality,
        ));
        Ok(success.into())
    }

    fn store_have_fn_equal_stmt_facts(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<InferResult, RuntimeError> {
        self.store_parameter_binding(&have_fn_equal_stmt.symbol_binding, ParamObjType::Identifier)?;

        let function_identifier_obj = self.declared_identifier_obj(have_fn_equal_stmt.name());
        let function_set_obj = fn_set_stored.clone().into();
        let function_in_function_set_fact = InFact::new(
            function_identifier_obj.clone(),
            function_set_obj,
            have_fn_equal_stmt.line_file.clone(),
        )
        .into();

        let infer_result = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state_and_reason(
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

    /// Mathematical contract: an explicit function definition has a
    /// well-formed function-set signature and an anonymous defining function
    /// that is universally meaningful and return-typed.
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

    /// Mathematical contract implementation: in an isolated scope, validate
    /// both the anonymous function (including `body in return_set`) and the
    /// function carrier that will be stored for its declared name.
    fn have_fn_equal_stmt_verify_well_defined_body(
        &mut self,
        have_fn_equal_stmt: &HaveFnEqualStmt,
        fn_set_stored: &FnSet,
    ) -> Result<(), RuntimeError> {
        let verify_state = UseContextVerifyState::new(0, false);

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
    ) -> Result<(Vec<StmtResult>, InferResult), RuntimeError> {
        let (verify_result, assumption_infers) =
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
        Ok((vec![verify_result], assumption_infers))
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
    ) -> Result<(StmtResult, InferResult), RuntimeError> {
        self.run_in_local_env(|rt| {
            let mut assumption_infers = InferResult::new();
            for param_def_with_set in have_fn_equal_stmt
                .equal_to_anonymous_fn
                .body
                .params_def_with_set
                .iter()
            {
                let param_infers = rt.define_params_with_set(param_def_with_set)?;
                assumption_infers.new_infer_result_inside(param_infers);
            }
            for dom_fact in have_fn_equal_stmt
                .equal_to_anonymous_fn
                .body
                .dom_facts
                .iter()
            {
                let mut dom_infers = rt
                    .store_or_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                        dom_fact.clone(),
                    )?;
                dom_infers
                    .relabel_all_added_facts_with_store_reason(ForallFact::premise_store_reason());
                assumption_infers.new_infer_result_inside(dom_infers);
            }
            let mut return_check = rt.verify_value_in_declared_return_set(
                (*have_fn_equal_stmt.equal_to_anonymous_fn.equal_to).clone(),
                (*have_fn_equal_stmt.equal_to_anonymous_fn.body.ret_set).clone(),
                have_fn_equal_stmt.line_file.clone(),
                &UseContextVerifyState::new(0, false),
            )?;
            rt.attach_known_fact_ids_to_infer_result(&mut assumption_infers)?;
            rt.attach_known_fact_ids_to_stmt_result(&mut return_check)?;
            Ok((return_check, assumption_infers))
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
}
