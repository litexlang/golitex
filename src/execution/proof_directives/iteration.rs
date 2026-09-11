use crate::prelude::*;

impl Runtime {
    pub fn exec_by_for_stmt(&mut self, stmt: &ByForStmt) -> Result<StmtResult, RuntimeError> {
        let expansion = stmt
            .expansion()
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;

        let corresponding_forall_fact = stmt
            .to_corresponding_forall_fact()
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;
        self.verify_forall_fact_params_and_dom_well_defined(
            &stmt.forall_fact,
            &VerifyState::initial(),
        )
        .map_err(|well_defined_error| {
            short_exec_error(
                stmt.clone().into(),
                format!(
                    "by for: forall parameters or domain is not well-defined (`{}`)",
                    stmt.forall_fact
                ),
                Some(well_defined_error),
                vec![],
            )
        })?;

        match expansion {
            ByForExpansion::Ranges { params, ranges } => {
                self.exec_by_for_ranges(stmt, &corresponding_forall_fact, &params, &ranges)
            }
            ByForExpansion::CartOfListSets { param, factors } => self
                .exec_by_for_cart_of_list_sets(stmt, &corresponding_forall_fact, &param, &factors),
        }
    }

    pub fn exec_by_for_stmt_affect_environment_only(
        &mut self,
        stmt: &ByForStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let corresponding_forall_fact = stmt
            .to_corresponding_forall_fact()
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;
        let infer_result = self.store_fact_with_trust_and_infer_with_reason(
            corresponding_forall_fact,
            InferReason::StatementWithVerification,
        )?;
        Ok(
            SuccessByStmtResult::ByForStmt(Box::new(SuccessByForStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: None,
            }))
            .into(),
        )
    }

    fn exec_by_for_ranges(
        &mut self,
        stmt: &ByForStmt,
        corresponding_forall_fact: &Fact,
        params: &[String],
        param_sets: &[ClosedRangeOrRange],
    ) -> Result<StmtResult, RuntimeError> {
        let evaluated_parameters = self
            .by_for_param_value_strings_of_each_param(stmt, param_sets)
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;
        let param_value_strings_of_each_param = evaluated_parameters
            .iter()
            .map(|(_, _, values)| values.clone())
            .collect::<Vec<_>>();
        let retained_parameter_results = params
            .iter()
            .zip(param_sets.iter())
            .zip(evaluated_parameters.iter())
            .map(
                |((parameter, range), (evaluated_start, evaluated_end, enumerated_values))| {
                    SuccessVerifyByForRangeParameterResult {
                        parameter: parameter.clone(),
                        range: range.clone(),
                        evaluated_start: evaluated_start.clone(),
                        evaluated_end: evaluated_end.clone(),
                        enumerated_values: enumerated_values.clone(),
                    }
                },
            )
            .collect::<Vec<_>>();
        let for_cartesian_product_is_empty = param_value_strings_of_each_param
            .iter()
            .any(|one_param_value_strings| one_param_value_strings.is_empty());
        if for_cartesian_product_is_empty {
            let infer_result_from_stored_forall_fact = self
                .store_with_well_defined_verification_and_infer_with_default_verify_state(
                    corresponding_forall_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by for: failed to store corresponding forall `{}`",
                            corresponding_forall_fact
                        ),
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
            let by_verification = SuccessVerifyByForResult::ranges(
                retained_parameter_results,
                stmt.forall_fact.to_string(),
                vec![],
                corresponding_forall_fact.to_string(),
            );
            return Ok(
                SuccessByStmtResult::ByForStmt(Box::new(SuccessByForStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result_from_stored_forall_fact),
                    verification: Some(by_verification),
                }))
                .into(),
            );
        }

        let mut current_parameter_index_assignment =
            Self::by_for_start_index_assignment(param_sets.len());
        let mut assignments = Vec::new();
        loop {
            let one_assignment_verification = self.exec_by_for_stmt_for_one_assignment(
                stmt,
                params,
                param_sets,
                &current_parameter_index_assignment,
                &param_value_strings_of_each_param,
            )?;
            assignments.push(one_assignment_verification);
            let next_parameter_index_assignment = Self::by_for_next_index_assignment(
                &current_parameter_index_assignment,
                &param_value_strings_of_each_param,
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
                        "by for: failed to store corresponding forall `{}`",
                        corresponding_forall_fact
                    ),
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        let by_verification = SuccessVerifyByForResult::ranges(
            retained_parameter_results,
            stmt.forall_fact.to_string(),
            assignments,
            corresponding_forall_fact.to_string(),
        );

        Ok(
            SuccessByStmtResult::ByForStmt(Box::new(SuccessByForStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result_from_stored_forall_fact),
                verification: Some(by_verification),
            }))
            .into(),
        )
    }

    fn exec_by_for_cart_of_list_sets(
        &mut self,
        stmt: &ByForStmt,
        corresponding_forall_fact: &Fact,
        param: &str,
        factors: &[ListSet],
    ) -> Result<StmtResult, RuntimeError> {
        let cartesian_product_is_empty = factors.iter().any(|ls| ls.list.is_empty());
        if cartesian_product_is_empty {
            let infer_result_from_stored_forall_fact = self
                .store_with_well_defined_verification_and_infer_with_default_verify_state(
                    corresponding_forall_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by for: failed to store corresponding forall `{}`",
                            corresponding_forall_fact
                        ),
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
            let by_verification = SuccessVerifyByForResult::cartesian_product_of_list_sets(
                param.to_string(),
                factors.to_vec(),
                stmt.forall_fact.to_string(),
                vec![],
                corresponding_forall_fact.to_string(),
            );
            return Ok(
                SuccessByStmtResult::ByForStmt(Box::new(SuccessByForStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(infer_result_from_stored_forall_fact),
                    verification: Some(by_verification),
                }))
                .into(),
            );
        }

        let mut current_assignment = vec![0; factors.len()];
        let mut assignments = Vec::new();
        loop {
            let one_assignment_verification =
                self.exec_by_for_cart_one_assignment(stmt, param, factors, &current_assignment)?;
            assignments.push(one_assignment_verification);
            match Self::by_for_cart_next_index_assignment(factors, &current_assignment) {
                Some(next) => current_assignment = next,
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
                        "by for: failed to store corresponding forall `{}`",
                        corresponding_forall_fact
                    ),
                    Some(store_fact_error),
                    vec![],
                )
            })?;

        let by_verification = SuccessVerifyByForResult::cartesian_product_of_list_sets(
            param.to_string(),
            factors.to_vec(),
            stmt.forall_fact.to_string(),
            assignments,
            corresponding_forall_fact.to_string(),
        );

        Ok(
            SuccessByStmtResult::ByForStmt(Box::new(SuccessByForStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result_from_stored_forall_fact),
                verification: Some(by_verification),
            }))
            .into(),
        )
    }

    fn by_for_cart_next_index_assignment(
        factors: &[ListSet],
        current_parameter_index_assignment: &[usize],
    ) -> Option<Vec<usize>> {
        let mut next = current_parameter_index_assignment.to_vec();
        for reversed_position in 0..next.len() {
            let position_from_right = next.len() - 1 - reversed_position;
            let current_index = next[position_from_right];
            let len = factors[position_from_right].list.len();
            if current_index + 1 < len {
                next[position_from_right] = current_index + 1;
                return Some(next);
            }
            next[position_from_right] = 0;
        }
        None
    }

    fn exec_by_for_cart_one_assignment(
        &mut self,
        stmt: &ByForStmt,
        param: &str,
        factors: &[ListSet],
        assignment: &[usize],
    ) -> Result<SuccessVerifyByAssignmentResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            let (param_binding, param_type) = stmt
                .forall_fact
                .typed_parameters
                .collect_param_bindings_with_types()
                .into_iter()
                .next()
                .expect("cartesian by-for has one parameter");
            rt.store_typed_parameter_binding(
                &param_binding,
                BindingScope::LocalBinder,
                &param_type,
            )?;
            let elems: Vec<Obj> = factors
                .iter()
                .enumerate()
                .map(|(i, ls)| (*ls.list[assignment[i]]).clone())
                .collect();
            let tuple_obj: Obj = Tuple::new(elems).into();
            let parameter_equal_to_tuple: AtomicFact = rt
                .new_equal_fact(
                    obj_for_bound_param_in_scope(&param_binding),
                    tuple_obj.clone(),
                    stmt.line_file.clone(),
                )
                .into();
            let assignment = vec![(param.to_string(), tuple_obj.to_string())];
            let assumption_fact: Fact = parameter_equal_to_tuple.clone().into();
            let assumption_infers = rt.store_atomic_fact_without_well_defined_verified_and_infer(
                parameter_equal_to_tuple,
            )?;
            let assumptions = vec![rt.freeze_by_assignment_assumption_result(
                assumption_fact,
                "for assignment",
                assumption_infers,
            )?];
            let (domain_checks, proof_steps, conclusion_checks) =
                rt.exec_by_for_stmt_dom_proof_then(stmt)?;
            Ok(SuccessVerifyByAssignmentResult::new(
                assignment,
                assumptions,
                domain_checks,
                proof_steps,
                conclusion_checks,
            ))
        })
    }
}

impl Runtime {
    // Negated domain: one atomic uses logical negation; conjunction uses De Morgan.
    #[deprecated(note = "use Runtime::negated_domain_fact_for_by_for_skip_with_runtime")]
    pub fn negated_domain_fact_for_by_for_skip(dom: &Fact) -> Option<Fact> {
        Self::negated_domain_fact_for_by_for_skip_with_runtime(&Runtime::default(), dom)
    }

    pub fn negated_domain_fact_for_by_for_skip_with_runtime(&self, dom: &Fact) -> Option<Fact> {
        match dom {
            Fact::AtomicFact(a) => a
                .logical_negation_with_runtime(self)
                .ok()
                .map(Fact::AtomicFact),
            Fact::AndFact(and_fact) => {
                if and_fact.facts.is_empty() {
                    return None;
                }
                let mut branches = Vec::with_capacity(and_fact.facts.len());
                for fact in and_fact.facts.iter() {
                    let negated = fact.logical_negation_with_runtime(self).ok()?;
                    branches.push(AndChainAtomicFact::AtomicFact(negated));
                }
                Some(self.new_or_fact(branches, and_fact.line_file()).into())
            }
            Fact::ChainFact(_)
            | Fact::OrFact(_)
            | Fact::ExistFact(_)
            | Fact::ForallFact(_)
            | Fact::ForallFactWithIff(_)
            | Fact::NotForall(_) => None,
        }
    }

    fn integer_string_from_number_like_obj_for_for(
        self: &Self,
        number_like_obj: &Obj,
        line_file: LineFile,
    ) -> Result<String, RuntimeError> {
        let calculated_string = {
            let value = self.resolve_obj_to_number(number_like_obj);

            match value {
                Some(number) => number.normalized_value,
                _ => {
                    return Err(UnknownRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            format!(
                            "by for: range boundary `{}` must be a calculable number expression",
                            number_like_obj
                        ),
                            line_file,
                        ),
                    )
                    .into());
                }
            }
        };

        if !is_number_string_literally_integer_without_dot(calculated_string.clone()) {
            return Err(
                UnknownRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "by for: range boundary `{}` is not an integer number",
                        number_like_obj
                    ),
                    line_file,
                ))
                .into(),
            );
        }
        Ok(calculated_string)
    }

    fn by_for_param_value_strings_of_each_param(
        self: &Self,
        stmt: &ByForStmt,
        param_sets: &[ClosedRangeOrRange],
    ) -> Result<Vec<(String, String, Vec<String>)>, String> {
        let mut evaluated_parameters = Vec::new();
        for param_set in param_sets.iter() {
            let (start_obj, end_obj, is_closed_range) = match param_set {
                ClosedRangeOrRange::ClosedRange(closed_range) => {
                    (closed_range.start.as_ref(), closed_range.end.as_ref(), true)
                }
                ClosedRangeOrRange::Range(range) => {
                    (range.start.as_ref(), range.end.as_ref(), false)
                }
            };
            let start_integer_string = self
                .integer_string_from_number_like_obj_for_for(start_obj, stmt.line_file.clone())
                .map_err(|e| e.to_string())?;
            let end_integer_string = self
                .integer_string_from_number_like_obj_for_for(end_obj, stmt.line_file.clone())
                .map_err(|e| e.to_string())?;
            let start_integer_i128 = start_integer_string.parse::<i128>().map_err(|_| {
                format!(
                    "by for: failed to parse start boundary `{}` as integer",
                    start_integer_string
                )
            })?;
            let end_integer_i128 = end_integer_string.parse::<i128>().map_err(|_| {
                format!(
                    "by for: failed to parse end boundary `{}` as integer",
                    end_integer_string
                )
            })?;

            let mut one_param_value_strings: Vec<String> = Vec::new();
            if start_integer_i128 <= end_integer_i128 {
                let right_boundary = if is_closed_range {
                    end_integer_i128
                } else {
                    end_integer_i128 - 1
                };
                if start_integer_i128 <= right_boundary {
                    let mut current_value_i128 = start_integer_i128;
                    while current_value_i128 <= right_boundary {
                        one_param_value_strings.push(current_value_i128.to_string());
                        current_value_i128 += 1;
                    }
                }
            }
            evaluated_parameters.push((
                start_integer_string,
                end_integer_string,
                one_param_value_strings,
            ));
        }
        Ok(evaluated_parameters)
    }

    fn by_for_start_index_assignment(param_count: usize) -> Vec<usize> {
        vec![0; param_count]
    }

    fn by_for_next_index_assignment(
        current_parameter_index_assignment: &Vec<usize>,
        param_value_strings_of_each_param: &Vec<Vec<String>>,
    ) -> Option<Vec<usize>> {
        let mut next_parameter_index_assignment = current_parameter_index_assignment.clone();
        for reversed_position in 0..next_parameter_index_assignment.len() {
            let position_from_right = next_parameter_index_assignment.len() - 1 - reversed_position;
            let current_index = next_parameter_index_assignment[position_from_right];
            let current_range_length = param_value_strings_of_each_param[position_from_right].len();
            if current_index + 1 < current_range_length {
                next_parameter_index_assignment[position_from_right] = current_index + 1;
                return Some(next_parameter_index_assignment);
            }
            next_parameter_index_assignment[position_from_right] = 0;
        }
        None
    }

    fn exec_by_for_stmt_for_one_assignment(
        &mut self,
        stmt: &ByForStmt,
        params: &[String],
        param_sets: &[ClosedRangeOrRange],
        parameter_index_assignment: &Vec<usize>,
        param_value_strings_of_each_param: &Vec<Vec<String>>,
    ) -> Result<SuccessVerifyByAssignmentResult, RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.exec_by_for_stmt_for_one_assignment_body(
                stmt,
                params,
                param_sets,
                parameter_index_assignment,
                param_value_strings_of_each_param,
            )
        })
    }

    fn exec_by_for_stmt_for_one_assignment_body(
        &mut self,
        stmt: &ByForStmt,
        params: &[String],
        _param_sets: &[ClosedRangeOrRange],
        parameter_index_assignment: &Vec<usize>,
        param_value_strings_of_each_param: &Vec<Vec<String>>,
    ) -> Result<SuccessVerifyByAssignmentResult, RuntimeError> {
        let mut assignment = Vec::new();
        let mut assumptions = Vec::new();
        let parameters = stmt
            .forall_fact
            .typed_parameters
            .collect_param_bindings_with_types();
        for (parameter_position, parameter_name) in params.iter().enumerate() {
            let (parameter_binding, parameter_type) = &parameters[parameter_position];
            let assigned_integer_string = param_value_strings_of_each_param[parameter_position]
                [parameter_index_assignment[parameter_position]]
                .clone();
            assignment.push((parameter_name.clone(), assigned_integer_string.clone()));
            self.store_typed_parameter_binding(
                parameter_binding,
                BindingScope::LocalBinder,
                parameter_type,
            )?;

            let parameter_in_z_atomic_fact = AtomicFact::InFact(self.new_in_fact(
                obj_for_bound_param_in_scope(parameter_binding),
                StandardSet::Z.into(),
                stmt.line_file.clone(),
            ));
            let parameter_in_z_fact: Fact = parameter_in_z_atomic_fact.clone().into();
            let parameter_in_z_infers = self
                .store_atomic_fact_without_well_defined_verified_and_infer(
                    parameter_in_z_atomic_fact,
                )?;
            assumptions.push(self.freeze_by_assignment_assumption_result(
                parameter_in_z_fact,
                "for range parameter",
                parameter_in_z_infers,
            )?);

            let parameter_equal_to_assigned_obj_atomic_fact =
                AtomicFact::EqualFact(self.new_equal_fact(
                    obj_for_bound_param_in_scope(parameter_binding),
                    Number::new(assigned_integer_string).into(),
                    stmt.line_file.clone(),
                ));
            let parameter_equal_to_assigned_obj_fact: Fact =
                parameter_equal_to_assigned_obj_atomic_fact.clone().into();
            let parameter_equal_to_assigned_obj_infers = self
                .store_atomic_fact_without_well_defined_verified_and_infer(
                    parameter_equal_to_assigned_obj_atomic_fact,
                )?;
            assumptions.push(self.freeze_by_assignment_assumption_result(
                parameter_equal_to_assigned_obj_fact,
                "for assignment",
                parameter_equal_to_assigned_obj_infers,
            )?);
        }

        let (domain_checks, proof_steps, conclusion_checks) =
            self.exec_by_for_stmt_dom_proof_then(stmt)?;
        Ok(SuccessVerifyByAssignmentResult::new(
            assignment,
            assumptions,
            domain_checks,
            proof_steps,
            conclusion_checks,
        ))
    }

    fn exec_by_for_stmt_dom_proof_then(
        &mut self,
        stmt: &ByForStmt,
    ) -> Result<
        (
            Vec<SuccessVerifyByAssignmentDomainResult>,
            Vec<StmtResult>,
            Vec<VerifyFactResult>,
        ),
        RuntimeError,
    > {
        let verify_state = VerifyState::initial();
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
                if let Some(negated_domain) =
                    self.negated_domain_fact_for_by_for_skip_with_runtime(dom_fact)
                {
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
                        return Ok((domain_checks, Vec::new(), Vec::new()));
                    }
                }
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                            "by for: domain fact `{}` is not decided (could not verify it or its negation)",
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
                self.verify_fact_allow_unknown(&fact_to_prove.clone().to_fact(), &verify_state)?;
            if verified_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!("by for: failed to prove `{}`", fact_to_prove),
                    None,
                    vec![],
                ));
            }
            conclusion_checks.push(verified_result);
        }
        Ok((domain_checks, proof_steps, conclusion_checks))
    }
}
