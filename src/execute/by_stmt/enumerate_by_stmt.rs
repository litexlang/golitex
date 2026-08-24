use crate::prelude::*;

impl Runtime {
    pub fn exec_by_enumerate_finite_set_stmt(
        &mut self,
        stmt: &ByEnumerateFiniteSetStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let (params, param_sets) = self
            .by_enumerate_finite_set_params(stmt)
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;

        let corresponding_forall_fact = stmt
            .to_corresponding_forall_fact()
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;

        self.verify_forall_fact_params_and_dom_well_defined(
            &stmt.forall_fact,
            &ProofSearchState::initial(),
        )
        .map_err(|well_defined_error| {
            short_exec_error(
                stmt.clone().into(),
                format!(
                    "by enumerate finite_set: forall parameters or domain is not well-defined (`{}`)",
                    stmt.forall_fact
                ),
                Some(well_defined_error),
                vec![],
            )
        })?;

        let enumerate_cartesian_product_is_empty =
            param_sets.iter().any(|list_set| list_set.list.is_empty());
        if enumerate_cartesian_product_is_empty {
            let infer_result_from_stored_forall_fact = self
                .store_with_well_defined_verification_and_infer_with_default_verify_state(
                    corresponding_forall_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by enumerate finite_set: failed to store corresponding forall `{}`",
                            corresponding_forall_fact
                        ),
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
            let infer_result = Self::infer_result_with_generated_forall_and_store_infer(
                &corresponding_forall_fact,
                infer_result_from_stored_forall_fact,
            );
            let by_verification = SuccessVerifyByEnumerateFiniteSetResult::new(
                params,
                param_sets.clone(),
                stmt.forall_fact.to_string(),
                vec![],
                corresponding_forall_fact.to_string(),
            );
            return Ok(SuccessByStmtResult::ByEnumerateFiniteSetStmt(Box::new(
                SuccessByEnumerateFiniteSetStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result),
                    verification: Some(by_verification),
                },
            ))
            .into());
        }

        let mut current_parameter_index_assignment =
            Self::by_enumerate_start_index_assignment(&param_sets);
        let mut assignments = Vec::new();
        loop {
            let one_assignment_verification = self.exec_by_enumerate_stmt_for_one_assignment(
                stmt,
                &params,
                &param_sets,
                &current_parameter_index_assignment,
            )?;
            assignments.push(one_assignment_verification);
            let next_parameter_index_assignment = Self::by_enumerate_next_index_assignment(
                &param_sets,
                &current_parameter_index_assignment,
            );
            match next_parameter_index_assignment {
                Some(next_parameter_index_assignment) => {
                    current_parameter_index_assignment = next_parameter_index_assignment;
                }
                None => break,
            }
        }

        let infer_result_from_stored_forall_fact = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                corresponding_forall_fact.clone(),
            )
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by enumerate finite_set: failed to store corresponding forall `{}`",
                        corresponding_forall_fact
                    ),
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        let infer_result = Self::infer_result_with_generated_forall_and_store_infer(
            &corresponding_forall_fact,
            infer_result_from_stored_forall_fact,
        );

        let by_verification = SuccessVerifyByEnumerateFiniteSetResult::new(
            params,
            param_sets,
            stmt.forall_fact.to_string(),
            assignments,
            corresponding_forall_fact.to_string(),
        );

        Ok(SuccessByStmtResult::ByEnumerateFiniteSetStmt(Box::new(
            SuccessByEnumerateFiniteSetStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(by_verification),
            },
        ))
        .into())
    }

    pub fn exec_by_enumerate_finite_set_stmt_affect_environment_only(
        &mut self,
        stmt: &ByEnumerateFiniteSetStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let corresponding_forall_fact = stmt
            .to_corresponding_forall_fact()
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            corresponding_forall_fact,
            InferReason::VerifiedStatement,
        )?;
        Ok(SuccessByStmtResult::ByEnumerateFiniteSetStmt(Box::new(
            SuccessByEnumerateFiniteSetStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: None,
            },
        ))
        .into())
    }

    fn infer_result_with_generated_forall_and_store_infer(
        generated_forall_fact: &Fact,
        infer_after_store: SuccessInferResult,
    ) -> SuccessInferResult {
        let mut infer_result = SuccessInferResult::new();
        infer_result.new_fact(generated_forall_fact);
        infer_result.new_infer_result_inside(infer_after_store);
        infer_result
    }

    fn by_enumerate_start_index_assignment(param_sets: &[ListSet]) -> Vec<usize> {
        let mut start_index_assignment: Vec<usize> = Vec::new();
        for _ in param_sets.iter() {
            start_index_assignment.push(0);
        }
        start_index_assignment
    }

    fn by_enumerate_next_index_assignment(
        param_sets: &[ListSet],
        current_parameter_index_assignment: &Vec<usize>,
    ) -> Option<Vec<usize>> {
        let mut next_parameter_index_assignment = current_parameter_index_assignment.clone();
        for reversed_position in 0..next_parameter_index_assignment.len() {
            let position_from_right = next_parameter_index_assignment.len() - 1 - reversed_position;
            let current_index = next_parameter_index_assignment[position_from_right];
            let current_list_set_length = param_sets[position_from_right].list.len();
            if current_index + 1 < current_list_set_length {
                next_parameter_index_assignment[position_from_right] = current_index + 1;
                return Some(next_parameter_index_assignment);
            }
            next_parameter_index_assignment[position_from_right] = 0;
        }
        None
    }

    fn exec_by_enumerate_stmt_for_one_assignment(
        &mut self,
        stmt: &ByEnumerateFiniteSetStmt,
        params: &[String],
        param_sets: &[ListSet],
        parameter_index_assignment: &Vec<usize>,
    ) -> Result<SuccessVerifyByAssignmentResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.exec_by_enumerate_stmt_for_one_assignment_body(
                stmt,
                params,
                param_sets,
                parameter_index_assignment,
            )
        })
    }

    fn exec_by_enumerate_stmt_for_one_assignment_body(
        &mut self,
        stmt: &ByEnumerateFiniteSetStmt,
        params: &[String],
        param_sets: &[ListSet],
        parameter_index_assignment: &Vec<usize>,
    ) -> Result<SuccessVerifyByAssignmentResult, RuntimeError> {
        let mut assignment = Vec::new();
        let mut assumptions = Vec::new();
        let param_bindings = stmt
            .forall_fact
            .params_def_with_type
            .collect_param_bindings();
        for (parameter_position, parameter_name) in params.iter().enumerate() {
            let parameter_binding = &param_bindings[parameter_position];
            let assigned_obj = (*param_sets[parameter_position].list
                [parameter_index_assignment[parameter_position]])
                .clone();
            assignment.push((parameter_name.clone(), assigned_obj.to_string()));
            self.store_parameter_binding(parameter_binding, ParamObjType::Forall)?;
            let parameter_equal_to_assigned_obj_atomic_fact: AtomicFact = EqualFact::new(
                obj_for_bound_param_in_scope(parameter_binding, ParamObjType::Forall),
                assigned_obj,
                stmt.line_file.clone(),
            )
            .into();
            let assumption_fact: Fact = parameter_equal_to_assigned_obj_atomic_fact.clone().into();
            let assumption_infers = self
                .store_atomic_fact_without_well_defined_verified_and_infer(
                    parameter_equal_to_assigned_obj_atomic_fact,
                )?;
            assumptions.push(self.freeze_by_assignment_assumption_result(
                assumption_fact,
                "enumerated assignment",
                assumption_infers,
            )?);
        }

        let verify_state = ProofSearchState::initial();
        let mut domain_checks = Vec::new();
        for dom_fact in stmt.forall_fact.dom_facts.iter() {
            let verify_dom_result = self.verify_fact_allow_unknown(dom_fact, &verify_state)?;
            if verify_dom_result.is_success() {
                let mut satisfied_infers = self
                    .store_with_well_defined_verification_and_infer_with_default_verify_state(
                        dom_fact.clone(),
                    )?;
                self.attach_known_fact_ids_to_infer_result(&mut satisfied_infers)?;
                domain_checks.push(SuccessVerifyByAssignmentDomainResult {
                    fact: dom_fact.clone(),
                    check: Box::new(verify_dom_result),
                    negated_check: None,
                    satisfied: true,
                    satisfied_infers: Some(satisfied_infers),
                });
            } else if verify_dom_result.is_unknown() {
                if let Some(negated_domain) = Self::negated_domain_fact_for_by_for_skip(dom_fact) {
                    let verify_negation_result =
                        self.verify_fact_allow_unknown(&negated_domain, &verify_state)?;
                    if verify_negation_result.is_success() {
                        domain_checks.push(SuccessVerifyByAssignmentDomainResult {
                            fact: dom_fact.clone(),
                            check: Box::new(verify_dom_result),
                            negated_check: Some(Box::new(verify_negation_result)),
                            satisfied: false,
                            satisfied_infers: None,
                        });
                        return Ok(SuccessVerifyByAssignmentResult::new(
                            assignment,
                            assumptions,
                            domain_checks,
                            Vec::new(),
                            Vec::new(),
                        ));
                    }
                }
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by enumerate finite_set: domain fact `{}` is not decided (could not verify it or its negation)",
                        dom_fact
                    ),
                    None,
                    vec![],
                ));
            }
        }

        let mut proof_steps = Vec::with_capacity(stmt.proof.len());
        for proof_stmt in stmt.proof.iter() {
            proof_steps.push(self.execute_statement(proof_stmt)?);
        }
        let mut conclusion_checks = Vec::with_capacity(stmt.forall_fact.then_facts.len());
        for fact_to_prove in stmt.forall_fact.then_facts.iter() {
            let verified_result =
                self.verify_exist_or_and_chain_atomic_fact(fact_to_prove, &verify_state)?;
            if verified_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by enumerate finite_set: failed to prove `{}`",
                        fact_to_prove
                    ),
                    None,
                    vec![],
                ));
            }
            conclusion_checks.push(verified_result);
        }
        Ok(SuccessVerifyByAssignmentResult::new(
            assignment,
            assumptions,
            domain_checks,
            proof_steps,
            conclusion_checks,
        ))
    }

    fn by_enumerate_finite_set_params(
        &self,
        stmt: &ByEnumerateFiniteSetStmt,
    ) -> Result<(Vec<String>, Vec<ListSet>), String> {
        let mut params = Vec::new();
        let mut param_sets = Vec::new();

        for group in stmt.forall_fact.params_def_with_type.groups.iter() {
            let list_set = match &group.param_type {
                ParamType::Obj(Obj::ListSet(list_set)) => list_set.clone(),
                ParamType::Obj(domain) => self
                    .get_all_obj_representatives_equal_to_given(domain)
                    .into_iter()
                    .find_map(|representative| match representative {
                        Obj::ListSet(list_set) => Some(list_set),
                        _ => None,
                    })
                    .ok_or_else(|| {
                        "by enumerate finite_set: each forall parameter type must be a list set `{ ... }` or a name equal to one"
                            .to_string()
                    })?,
                _ => {
                    return Err(
                        "by enumerate finite_set: each forall parameter type must be a list set `{ ... }` or a name equal to one"
                            .to_string(),
                    );
                }
            };

            for name in group.params.iter() {
                params.push(name.name().to_string());
                param_sets.push(list_set.clone());
            }
        }

        if params.is_empty() {
            return Err(
                "by enumerate finite_set: forall must declare at least one parameter".to_string(),
            );
        }

        Ok((params, param_sets))
    }
}
