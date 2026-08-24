use crate::prelude::*;

use super::exec_have_fn_equal_shared::case_conditions_are_disjoint_result;

impl Runtime {
    pub fn exec_have_fn_by_induc(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let well_definedness_run_in_local_env =
            self.exec_have_fn_by_induc_verify_well_definedness(stmt)?;
        let verification_run_in_local_env = self.exec_have_fn_by_induc_verify_process(stmt)?;
        let infer_result = self.exec_have_fn_by_induc_affect_environment(stmt)?;

        Ok(
            SuccessDefObjStmtResult::HaveFnByInducStmt(Box::new(SuccessHaveFnByInducStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(SuccessVerifyHaveFnByInducResult {
                    well_definedness_run_in_local_env,
                    verification_run_in_local_env,
                }),
            }))
            .into(),
        )
    }

    pub fn exec_have_fn_by_induc_affect_environment(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let flat = stmt.to_have_fn_equal_case_by_case_stmt();
        let fn_set_stored = self
            .fn_set_from_fn_set_clause(&flat.fn_set_clause)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        self.store_have_fn_equal_case_by_case_stmt_facts(&flat, &fn_set_stored)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))
    }

    pub fn exec_have_fn_by_induc_stmt_affect_environment_only(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_have_fn_by_induc_affect_environment(stmt)?;
        Ok(
            SuccessDefObjStmtResult::HaveFnByInducStmt(Box::new(SuccessHaveFnByInducStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: None,
            }))
            .into(),
        )
    }

    fn have_fn_by_induc_err(stmt: &HaveFnByInducStmt, cause: RuntimeError) -> RuntimeError {
        exec_stmt_error_with_stmt_and_cause(stmt.clone().into(), cause)
    }

    fn exec_have_fn_by_induc_verify_process(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<SuccessVerifyHaveFnByInducLocalEnvResult, RuntimeError> {
        self.run_in_local_env(|rt| rt.exec_have_fn_by_induc_verify_process_body(stmt))
    }

    fn exec_have_fn_by_induc_verify_process_body(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<SuccessVerifyHaveFnByInducLocalEnvResult, RuntimeError> {
        let parameters_and_domain = self.define_have_fn_by_induc_current_params_and_domain(stmt)?;
        let measure = self.verify_have_fn_by_induc_integer_measure_and_lower_bound(stmt)?;
        let recursive_function = self.register_have_fn_by_induc_recursive_fn(stmt)?;
        let cases = self.verify_have_fn_by_induc_case_list(stmt, &stmt.cases)?;
        Ok(SuccessVerifyHaveFnByInducLocalEnvResult {
            parameters_and_domain,
            measure,
            recursive_function,
            cases,
        })
    }

    /// Mathematical contract: an inductive function declaration has a fresh
    /// name, a meaningful function signature, and well-defined measure and
    /// lower-bound expressions under its parameter domain. Integrality,
    /// descent, cases, and return values are checked in the proof phase.
    fn exec_have_fn_by_induc_verify_well_definedness(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<SuccessVerifyHaveFnByInducWellDefinednessLocalEnvResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.store_parameter_binding(&stmt.symbol_binding, ParamObjType::Identifier)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            let fn_set = rt
                .fn_set_from_fn_set_clause(&stmt.fn_set_clause)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            let function_set_well_definedness = rt
                .verify_obj_well_defined_result(
                    &Obj::from(fn_set.clone()),
                    &UseContextVerifyState::new(0, false),
                )
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            let parameters_and_domain =
                rt.define_have_fn_by_induc_current_params_and_domain(stmt)?;
            let measure_well_definedness = rt
                .verify_obj_well_defined_result(
                    &stmt.measure,
                    &UseContextVerifyState::new(0, false),
                )
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            let lower_bound_well_definedness = rt
                .verify_obj_well_defined_result(
                    &stmt.lower_bound,
                    &UseContextVerifyState::new(0, false),
                )
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            Ok(SuccessVerifyHaveFnByInducWellDefinednessLocalEnvResult {
                function_binding: stmt.symbol_binding.clone(),
                function_set: fn_set,
                function_set_well_definedness,
                parameters_and_domain,
                measure_well_definedness,
                lower_bound_well_definedness,
            })
        })
    }

    fn define_have_fn_by_induc_current_params_and_domain(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<SuccessVerifyHaveFnByInducParametersAndDomainResult, RuntimeError> {
        let mut parameter_groups = Vec::with_capacity(stmt.fn_set_clause.params_def_with_set.len());
        for (group_index, param_def_with_set) in
            stmt.fn_set_clause.params_def_with_set.iter().enumerate()
        {
            let mut infers = self
                .define_params_with_set(param_def_with_set)
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            self.attach_known_fact_ids_to_infer_result(&mut infers)?;
            parameter_groups.push(SuccessVerifyHaveFnByInducParameterGroupResult {
                group_index,
                definition: param_def_with_set.clone(),
                infers,
            });
        }

        let mut domain_facts = Vec::with_capacity(stmt.fn_set_clause.dom_facts.len());
        for (domain_index, dom_fact) in stmt.fn_set_clause.dom_facts.iter().enumerate() {
            let fact: Fact = dom_fact.clone().into();
            let mut infers = self
                .store_quantifier_free_fact_without_well_defined_verified_and_infer(
                    dom_fact.clone(),
                )
                .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
            self.attach_known_fact_ids_to_infer_result(&mut infers)?;
            let fact_id = self.known_fact_id_for_fact(&fact)?;
            domain_facts.push(SuccessVerifyHaveFnByInducDomainFactResult {
                domain_index,
                store: SuccessStoreFactResult {
                    fact,
                    fact_id,
                    infers,
                },
            });
        }

        Ok(SuccessVerifyHaveFnByInducParametersAndDomainResult {
            parameter_groups,
            domain_facts,
        })
    }

    fn verify_have_fn_by_induc_integer_measure_and_lower_bound(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<SuccessVerifyHaveFnByInducMeasureResult, RuntimeError> {
        let measure_well_definedness = self
            .verify_obj_well_defined_result(&stmt.measure, &UseContextVerifyState::new(0, false))
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        let lower_bound_well_definedness = self
            .verify_obj_well_defined_result(
                &stmt.lower_bound,
                &UseContextVerifyState::new(0, false),
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let measure_integer_check =
            self.verify_have_fn_by_induc_integer_object(stmt, "measure", &stmt.measure)?;
        let lower_bound_integer_check =
            self.verify_have_fn_by_induc_integer_object(stmt, "lower bound", &stmt.lower_bound)?;

        let lower_fact: AtomicFact = GreaterEqualFact::new(
            stmt.measure.clone(),
            stmt.lower_bound.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let mut lower_bound_check = self
            .verify_atomic_fact(&lower_fact, &UseContextVerifyState::new(0, false))
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        if lower_bound_check.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "have_fn_by_induc: failed to prove decreasing measure lower bound `{}`",
                    lower_fact
                ),
                None,
                vec![],
            ));
        }
        self.attach_known_fact_ids_to_stmt_result(&mut lower_bound_check)?;
        Ok(SuccessVerifyHaveFnByInducMeasureResult {
            measure_well_definedness,
            lower_bound_well_definedness,
            measure_integer_check: Box::new(measure_integer_check),
            lower_bound_integer_check: Box::new(lower_bound_integer_check),
            lower_bound_check: Box::new(lower_bound_check),
        })
    }

    fn verify_have_fn_by_induc_integer_object(
        &mut self,
        stmt: &HaveFnByInducStmt,
        label: &str,
        object: &Obj,
    ) -> Result<StmtResult, RuntimeError> {
        let integer_fact: AtomicFact = InFact::new(
            object.clone(),
            StandardSet::Z.into(),
            stmt.line_file.clone(),
        )
        .into();
        let mut result = self
            .verify_atomic_fact(&integer_fact, &UseContextVerifyState::new(0, false))
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "have fn by induc: failed to verify that the {} is integer-valued",
                        label
                    ),
                    Some(e),
                    vec![],
                )
            })?;
        if result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "have fn by induc: the {} must be provably integer-valued; failed to prove `{}`",
                    label, integer_fact
                ),
                None,
                vec![],
            ));
        }
        self.attach_known_fact_ids_to_stmt_result(&mut result)?;
        Ok(result)
    }

    fn register_have_fn_by_induc_recursive_fn(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<SuccessVerifyHaveFnByInducRecursiveFunctionResult, RuntimeError> {
        self.store_parameter_binding(&stmt.symbol_binding, ParamObjType::Identifier)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let source_bindings = stmt
            .fn_set_clause
            .params_def_with_set
            .collect_param_bindings();
        let (_, param_to_generated_obj) =
            self.fresh_binder_retag_plan_for_bindings(&source_bindings, ParamObjType::FnSet);

        let generated_body = self
            .alpha_rename_fn_set_body(
                &FnSetBody::new(
                    stmt.fn_set_clause.params_def_with_set.clone(),
                    stmt.fn_set_clause.dom_facts.clone(),
                    stmt.fn_set_clause.ret_set.clone(),
                ),
                &param_to_generated_obj,
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        let generated_groups = generated_body.params_def_with_set;
        let mut recursive_dom_facts = generated_body.dom_facts;

        let generated_measure = self
            .inst_obj(
                &stmt.measure,
                &param_to_generated_obj,
                ParamObjType::AlphaRename,
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        recursive_dom_facts.push(QuantifierFreeFact::AtomicFact(
            LessFact::new(
                generated_measure.clone(),
                stmt.measure.clone(),
                stmt.line_file.clone(),
            )
            .into(),
        ));
        recursive_dom_facts.push(QuantifierFreeFact::AtomicFact(
            GreaterEqualFact::new(
                generated_measure,
                stmt.lower_bound.clone(),
                stmt.line_file.clone(),
            )
            .into(),
        ));

        let generated_ret_set = *generated_body.ret_set;
        let recursive_fn_set = self
            .new_fn_set(generated_groups, recursive_dom_facts, generated_ret_set)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let function_in_function_set_fact: Fact = InFact::new(
            self.declared_identifier_obj(stmt.name()),
            recursive_fn_set.clone().into(),
            stmt.line_file.clone(),
        )
        .into();

        let mut infers = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                function_in_function_set_fact.clone(),
            )
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        self.attach_known_fact_ids_to_infer_result(&mut infers)?;
        let fact_id = self.known_fact_id_for_fact(&function_in_function_set_fact)?;
        Ok(SuccessVerifyHaveFnByInducRecursiveFunctionResult {
            function_set: recursive_fn_set,
            membership_store: SuccessStoreFactResult {
                fact: function_in_function_set_fact,
                fact_id,
                infers,
            },
        })
    }

    fn verify_have_fn_by_induc_case_list(
        &mut self,
        stmt: &HaveFnByInducStmt,
        cases: &[HaveFnByInducCase],
    ) -> Result<SuccessVerifyHaveFnByInducCaseListResult, RuntimeError> {
        if cases.is_empty() {
            return Err(short_exec_error(
                stmt.clone().into(),
                "have_fn_by_induc: case list must not be empty".to_string(),
                None,
                vec![],
            ));
        }

        let coverage_cases: Vec<AndChainAtomicFact> =
            cases.iter().map(|c| c.case_fact.clone()).collect();
        let coverage: Fact = OrFact::new(coverage_cases, stmt.line_file.clone()).into();
        let mut coverage_check = self
            .verify_fact_return_err_if_not_true(&coverage, &UseContextVerifyState::new(0, false))
            .map_err(|e| {
                short_exec_error(
                    stmt.clone().into(),
                    "have_fn_by_induc: cases do not cover all situations".to_string(),
                    Some(e),
                    vec![],
                )
            })?;
        self.attach_known_fact_ids_to_stmt_result(&mut coverage_check)?;

        let mutual_exclusions =
            self.verify_have_fn_by_induc_cases_mutually_exclusive(stmt, cases)?;

        let mut case_results = Vec::with_capacity(cases.len());
        for (case_index, case) in cases.iter().enumerate() {
            let case_result = self.run_in_local_env(|rt| {
                let case_fact = Fact::from(case.case_fact.clone());
                let mut infers = rt
                    .store_with_well_defined_verification_and_infer_with_default_verify_state(
                        case_fact.clone(),
                    )
                    .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
                rt.attach_known_fact_ids_to_infer_result(&mut infers)?;
                let fact_id = rt.known_fact_id_for_fact(&case_fact)?;
                let assumption_store = SuccessStoreFactResult {
                    fact: case_fact.clone(),
                    fact_id,
                    infers,
                };

                let body = match &case.body {
                    HaveFnByInducCaseBody::EqualTo(equal_to) => {
                        SuccessVerifyHaveFnByInducCaseBodyResult::EqualTo(Box::new(
                            rt.verify_have_fn_by_induc_equal_to(stmt, equal_to)?,
                        ))
                    }
                    HaveFnByInducCaseBody::NestedCases(nested) => {
                        SuccessVerifyHaveFnByInducCaseBodyResult::NestedCases(Box::new(
                            rt.verify_have_fn_by_induc_case_list(stmt, nested)?,
                        ))
                    }
                };
                Ok::<SuccessVerifyHaveFnByInducCaseResult, RuntimeError>(
                    SuccessVerifyHaveFnByInducCaseResult {
                        case_index,
                        case_fact,
                        assumption_store,
                        body,
                    },
                )
            })?;
            case_results.push(case_result);
        }

        Ok(SuccessVerifyHaveFnByInducCaseListResult {
            coverage_fact: coverage,
            coverage_check: Box::new(coverage_check),
            mutual_exclusions,
            cases: case_results,
        })
    }

    fn verify_have_fn_by_induc_equal_to(
        &mut self,
        stmt: &HaveFnByInducStmt,
        equal_to: &Obj,
    ) -> Result<SuccessVerifyHaveFnByInducEqualToResult, RuntimeError> {
        let verify_state = UseContextVerifyState::new(0, false);
        let well_definedness = self
            .verify_obj_well_defined_result(equal_to, &verify_state)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;

        let equal_to_in_ret_set_atomic_fact: AtomicFact = InFact::new(
            equal_to.clone(),
            stmt.fn_set_clause.ret_set.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let mut return_membership_check = self
            .verify_atomic_fact(&equal_to_in_ret_set_atomic_fact, &verify_state)
            .map_err(|e| Self::have_fn_by_induc_err(stmt, e))?;
        if return_membership_check.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                format!(
                    "have_fn_by_induc: {} is not in return set {}",
                    equal_to, stmt.fn_set_clause.ret_set
                ),
                None,
                vec![],
            ));
        }
        self.attach_known_fact_ids_to_stmt_result(&mut return_membership_check)?;
        Ok(SuccessVerifyHaveFnByInducEqualToResult {
            value: equal_to.clone(),
            well_definedness,
            return_membership_fact: equal_to_in_ret_set_atomic_fact,
            return_membership_check: Box::new(return_membership_check),
        })
    }

    fn verify_have_fn_by_induc_cases_mutually_exclusive(
        &mut self,
        stmt: &HaveFnByInducStmt,
        cases: &[HaveFnByInducCase],
    ) -> Result<Vec<SuccessVerifyCaseDisjointnessResult>, RuntimeError> {
        let mut results = Vec::new();
        for i in 0..cases.len() {
            for j in (i + 1)..cases.len() {
                let Some(result) = case_conditions_are_disjoint_result(
                    self,
                    i,
                    j,
                    &cases[i].case_fact,
                    &cases[j].case_fact,
                )?
                else {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "have_fn_by_induc: cases overlap or cannot be proved mutually exclusive: `{}` and `{}`",
                            cases[i].case_fact, cases[j].case_fact
                        ),
                        None,
                        vec![],
                    ));
                };
                results.push(result);
            }
        }
        Ok(results)
    }

    pub fn exec_have_fn_by_induc_stmt(
        &mut self,
        stmt: &HaveFnByInducStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.exec_have_fn_by_induc(stmt)
    }
}
