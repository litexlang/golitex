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
            &VerifyState::new(0, false),
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

    fn exec_by_for_ranges(
        &mut self,
        stmt: &ByForStmt,
        corresponding_forall_fact: &Fact,
        params: &[String],
        param_sets: &[ClosedRangeOrRange],
    ) -> Result<StmtResult, RuntimeError> {
        let param_value_strings_of_each_param = self
            .by_for_param_value_strings_of_each_param(stmt, param_sets)
            .map_err(|msg| short_exec_error(stmt.clone().into(), msg, None, vec![]))?;
        let for_cartesian_product_is_empty = param_value_strings_of_each_param
            .iter()
            .any(|one_param_value_strings| one_param_value_strings.is_empty());
        if for_cartesian_product_is_empty {
            let infer_result_from_stored_forall_fact = self
                .verify_well_defined_and_store_and_infer_with_default_verify_state(
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
            let by_verification = ByForVerificationResult::new(
                "ranges".to_string(),
                params.to_vec(),
                param_sets
                    .iter()
                    .map(|param_set| param_set.to_string())
                    .collect(),
                stmt.forall_fact.to_string(),
                vec![],
                corresponding_forall_fact.to_string(),
            );
            return Ok((NonFactualStmtSuccess::new_with_by_verification(
                stmt.clone().into(),
                infer_result_from_stored_forall_fact,
                vec![],
                by_verification.into(),
            ))
            .into());
        }

        let mut current_parameter_index_assignment =
            Self::by_for_start_index_assignment(param_sets.len());
        let mut inside_results = Vec::new();
        let mut assignments = Vec::new();
        loop {
            let (mut one_assignment_results, one_assignment_verification) = self
                .exec_by_for_stmt_for_one_assignment(
                    stmt,
                    params,
                    param_sets,
                    &current_parameter_index_assignment,
                    &param_value_strings_of_each_param,
                )?;
            inside_results.append(&mut one_assignment_results);
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
            .verify_well_defined_and_store_and_infer_with_default_verify_state(
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

        let by_verification = ByForVerificationResult::new(
            "ranges".to_string(),
            params.to_vec(),
            param_sets
                .iter()
                .map(|param_set| param_set.to_string())
                .collect(),
            stmt.forall_fact.to_string(),
            assignments,
            corresponding_forall_fact.to_string(),
        );

        Ok((NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result_from_stored_forall_fact,
            inside_results,
            by_verification.into(),
        ))
        .into())
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
                .verify_well_defined_and_store_and_infer_with_default_verify_state(
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
            let by_verification = ByForVerificationResult::new(
                "cart_of_list_sets".to_string(),
                vec![param.to_string()],
                factors.iter().map(|factor| factor.to_string()).collect(),
                stmt.forall_fact.to_string(),
                vec![],
                corresponding_forall_fact.to_string(),
            );
            return Ok((NonFactualStmtSuccess::new_with_by_verification(
                stmt.clone().into(),
                infer_result_from_stored_forall_fact,
                vec![],
                by_verification.into(),
            ))
            .into());
        }

        let mut current_assignment = vec![0; factors.len()];
        let mut inside_results = Vec::new();
        let mut assignments = Vec::new();
        loop {
            let (mut one_assignment_results, one_assignment_verification) =
                self.exec_by_for_cart_one_assignment(stmt, param, factors, &current_assignment)?;
            inside_results.append(&mut one_assignment_results);
            assignments.push(one_assignment_verification);
            match Self::by_for_cart_next_index_assignment(factors, &current_assignment) {
                Some(next) => current_assignment = next,
                None => break,
            }
        }

        let infer_result_from_stored_forall_fact = self
            .verify_well_defined_and_store_and_infer_with_default_verify_state(
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

        let by_verification = ByForVerificationResult::new(
            "cart_of_list_sets".to_string(),
            vec![param.to_string()],
            factors.iter().map(|factor| factor.to_string()).collect(),
            stmt.forall_fact.to_string(),
            assignments,
            corresponding_forall_fact.to_string(),
        );

        Ok((NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            infer_result_from_stored_forall_fact,
            inside_results,
            by_verification.into(),
        ))
        .into())
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
    ) -> Result<(Vec<StmtResult>, ByAssignmentVerificationResult), RuntimeError> {
        self.run_in_local_env(|rt| {
            rt.store_free_param_or_identifier_name(param, ParamObjType::Forall)?;
            let elems: Vec<Obj> = factors
                .iter()
                .enumerate()
                .map(|(i, ls)| (*ls.list[assignment[i]]).clone())
                .collect();
            let tuple_obj: Obj = Tuple::new(elems).into();
            let parameter_equal_to_tuple: AtomicFact = EqualFact::new(
                obj_for_bound_param_in_scope(param.to_string(), ParamObjType::Forall),
                tuple_obj.clone(),
                stmt.line_file.clone(),
            )
            .into();
            let assignment = vec![(param.to_string(), tuple_obj.to_string())];
            let assumptions = vec![(
                parameter_equal_to_tuple.to_string(),
                "for assignment".to_string(),
            )];
            rt.store_atomic_fact_without_well_defined_verified_and_infer(parameter_equal_to_tuple)?;
            let (
                inside_results,
                domain_check_count,
                proof_step_count,
                conclusion_count,
                skipped_domain,
            ) = rt.exec_by_for_stmt_dom_proof_then(stmt)?;
            let result_count = inside_results.len();
            let verification = ByAssignmentVerificationResult::new(
                assignment,
                assumptions,
                domain_check_count,
                proof_step_count,
                conclusion_count,
                skipped_domain,
                result_count,
            );
            Ok((inside_results, verification))
        })
    }
}

impl Runtime {
    // Negated domain: one atomic uses `make_reversed`; conjunction uses De Morgan (or of negated atomics).
    pub(crate) fn negated_domain_fact_for_by_for_skip(dom: &Fact) -> Option<Fact> {
        match dom {
            Fact::AtomicFact(a) => Some(Fact::AtomicFact(a.make_reversed())),
            Fact::AndFact(and_fact) => {
                if and_fact.facts.is_empty() {
                    return None;
                }
                let branches: Vec<AndChainAtomicFact> = and_fact
                    .facts
                    .iter()
                    .map(|f| AndChainAtomicFact::AtomicFact(f.make_reversed()))
                    .collect();
                Some(OrFact::new(branches, and_fact.line_file()).into())
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
    ) -> Result<Vec<Vec<String>>, String> {
        let mut param_value_strings_of_each_param: Vec<Vec<String>> = Vec::new();
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
            param_value_strings_of_each_param.push(one_param_value_strings);
        }
        Ok(param_value_strings_of_each_param)
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
    ) -> Result<(Vec<StmtResult>, ByAssignmentVerificationResult), RuntimeError> {
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
    ) -> Result<(Vec<StmtResult>, ByAssignmentVerificationResult), RuntimeError> {
        let mut assignment = Vec::new();
        let mut assumptions = Vec::new();
        for (parameter_position, parameter_name) in params.iter().enumerate() {
            let assigned_integer_string = param_value_strings_of_each_param[parameter_position]
                [parameter_index_assignment[parameter_position]]
                .clone();
            assignment.push((parameter_name.clone(), assigned_integer_string.clone()));
            self.store_free_param_or_identifier_name(parameter_name, ParamObjType::Forall)?;

            let parameter_in_z_atomic_fact = AtomicFact::InFact(InFact::new(
                obj_for_bound_param_in_scope(parameter_name.to_string(), ParamObjType::Forall),
                StandardSet::Z.into(),
                stmt.line_file.clone(),
            ));
            assumptions.push((
                parameter_in_z_atomic_fact.to_string(),
                "for range parameter".to_string(),
            ));
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                parameter_in_z_atomic_fact,
            )?;

            let parameter_equal_to_assigned_obj_atomic_fact =
                AtomicFact::EqualFact(EqualFact::new(
                    obj_for_bound_param_in_scope(parameter_name.to_string(), ParamObjType::Forall),
                    Number::new(assigned_integer_string).into(),
                    stmt.line_file.clone(),
                ));
            assumptions.push((
                parameter_equal_to_assigned_obj_atomic_fact.to_string(),
                "for assignment".to_string(),
            ));
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                parameter_equal_to_assigned_obj_atomic_fact,
            )?;
        }

        let (
            inside_results,
            domain_check_count,
            proof_step_count,
            conclusion_count,
            skipped_domain,
        ) = self.exec_by_for_stmt_dom_proof_then(stmt)?;
        let result_count = inside_results.len();
        let verification = ByAssignmentVerificationResult::new(
            assignment,
            assumptions,
            domain_check_count,
            proof_step_count,
            conclusion_count,
            skipped_domain,
            result_count,
        );
        Ok((inside_results, verification))
    }

    fn exec_by_for_stmt_dom_proof_then(
        &mut self,
        stmt: &ByForStmt,
    ) -> Result<(Vec<StmtResult>, usize, usize, usize, Option<String>), RuntimeError> {
        let verify_state = VerifyState::new(0, false);
        let mut inside_results = Vec::new();
        let mut domain_check_count = 0;
        let mut skipped_domain = None;
        for dom_fact in stmt.forall_fact.dom_facts.iter() {
            let verify_dom_result = self.verify_fact_full(dom_fact, &verify_state)?;
            if verify_dom_result.is_true() {
                self.verify_well_defined_and_store_and_infer_with_default_verify_state(
                    dom_fact.clone(),
                )?;
                inside_results.push(verify_dom_result);
                domain_check_count += 1;
            } else if verify_dom_result.is_unknown() {
                inside_results.push(verify_dom_result);
                domain_check_count += 1;
                if let Some(negated_domain) = Self::negated_domain_fact_for_by_for_skip(dom_fact) {
                    let verify_negation_result =
                        self.verify_fact_full(&negated_domain, &verify_state)?;
                    if verify_negation_result.is_true() {
                        inside_results.push(verify_negation_result);
                        domain_check_count += 1;
                        skipped_domain = Some(dom_fact.to_string());
                        return Ok((inside_results, domain_check_count, 0, 0, skipped_domain));
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

        let proof_step_count = stmt.proof.len();
        for proof_stmt in stmt.proof.iter() {
            inside_results.push(self.exec_stmt(proof_stmt)?);
        }
        let mut conclusion_count = 0;
        for fact_to_prove in stmt.forall_fact.then_facts.iter() {
            let verified_result =
                self.verify_exist_or_and_chain_atomic_fact(fact_to_prove, &verify_state)?;
            if verified_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!("by for: failed to prove `{}`", fact_to_prove),
                    None,
                    vec![],
                ));
            }
            inside_results.push(verified_result);
            conclusion_count += 1;
        }
        Ok((
            inside_results,
            domain_check_count,
            proof_step_count,
            conclusion_count,
            skipped_domain,
        ))
    }
}
