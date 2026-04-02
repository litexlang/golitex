use crate::prelude::*;

impl Runtime {
    pub fn exec_for_axiom_stmt(
        &mut self,
        stmt: &ForAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        if stmt.params.len() != stmt.param_sets.len() {
            return Err(RuntimeError::from(
                ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    "by for: number of params does not match number of ranges".to_string(),
                    None,
                    vec![],
                ),
            ));
        }

        let corresponding_forall_fact = stmt.to_corresponding_forall_fact().map_err(|msg| {
            RuntimeError::from(ExecStmtError::with_message_and_cause(
                Stmt::ForAxiomStmt(stmt.clone()),
                msg,
                None,
                vec![],
            ))
        })?;
        self.verify_fact_well_defined(&corresponding_forall_fact, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::from(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    format!(
                        "by for: corresponding forall `{}` is not well-defined",
                        corresponding_forall_fact
                    ),
                    Some(well_defined_error.into()),
                    vec![],
                ))
            })?;

        let param_value_strings_of_each_param = self
            .for_param_value_strings_of_each_param(stmt)
            .map_err(|msg| {
                RuntimeError::from(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    msg,
                    None,
                    vec![],
                ))
            })?;
        let for_cartesian_product_is_empty = param_value_strings_of_each_param
            .iter()
            .any(|one_param_value_strings| one_param_value_strings.is_empty());
        if for_cartesian_product_is_empty {
            let infer_result_from_stored_forall_fact = self
                .store_fact_without_well_defined_verified_and_infer(
                    corresponding_forall_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    RuntimeError::from(ExecStmtError::with_message_and_cause(
                        Stmt::ForAxiomStmt(stmt.clone()),
                        format!(
                            "by for: failed to store corresponding forall `{}`",
                            corresponding_forall_fact
                        ),
                        Some(store_fact_error.into()),
                        vec![],
                    ))
                })?;
            return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    infer_result_from_stored_forall_fact,
                    vec![],
                ),
            ));
        }

        let mut all_inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        let mut current_parameter_index_assignment = Self::for_start_index_assignment(stmt);
        loop {
            let mut one_assignment_inside_results = self.exec_for_axiom_stmt_for_one_assignment(
                stmt,
                &current_parameter_index_assignment,
                &param_value_strings_of_each_param,
            )?;
            all_inside_results.append(&mut one_assignment_inside_results);
            let next_parameter_index_assignment = Self::for_next_index_assignment(
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
            .store_fact_without_well_defined_verified_and_infer(
                corresponding_forall_fact.clone(),
            )
            .map_err(|store_fact_error| {
                RuntimeError::from(ExecStmtError::with_message_and_cause(
                    Stmt::ForAxiomStmt(stmt.clone()),
                    format!(
                        "by for: failed to store corresponding forall `{}`",
                        corresponding_forall_fact
                    ),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ForAxiomStmt(stmt.clone()),
                infer_result_from_stored_forall_fact,
                all_inside_results,
            ),
        ))
    }
}

impl Runtime {
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
                    return Err(UnknownError::new(
                        format!(
                            "by for: range boundary `{}` must be a calculable number expression",
                            number_like_obj
                        ),
                        line_file,
                        None,
                        None,
                    ).into());
                }
            }
        };

        if !is_number_string_literally_integer_without_dot(calculated_string.clone()) {
            return Err(UnknownError::new(
                format!(
                    "by for: range boundary `{}` is not an integer number",
                    number_like_obj
                ),
                line_file,
                None,
                None,
            ).into());
        }
        Ok(calculated_string)
    }

    fn for_param_value_strings_of_each_param(
        self: &Self,
        stmt: &ForAxiomStmt,
    ) -> Result<Vec<Vec<String>>, String> {
        let mut param_value_strings_of_each_param: Vec<Vec<String>> = Vec::new();
        for param_set in stmt.param_sets.iter() {
            let (start_obj, end_obj, is_closed_range) = match param_set {
                crate::stmt::axiom_stmt::ClosedRangeOrRange::ClosedRange(closed_range) => {
                    (closed_range.start.as_ref(), closed_range.end.as_ref(), true)
                }
                crate::stmt::axiom_stmt::ClosedRangeOrRange::Range(range) => {
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

    fn for_start_index_assignment(stmt: &ForAxiomStmt) -> Vec<usize> {
        let mut start_index_assignment: Vec<usize> = Vec::new();
        for _ in stmt.param_sets.iter() {
            start_index_assignment.push(0);
        }
        start_index_assignment
    }

    fn for_next_index_assignment(
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

    fn exec_for_axiom_stmt_for_one_assignment(
        &mut self,
        stmt: &ForAxiomStmt,
        parameter_index_assignment: &Vec<usize>,
        param_value_strings_of_each_param: &Vec<Vec<String>>,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        self.push_env();
        let execute_result = self.exec_for_axiom_stmt_for_one_assignment_body(
            stmt,
            parameter_index_assignment,
            param_value_strings_of_each_param,
        );
        self.pop_env();
        execute_result
    }

    fn exec_for_axiom_stmt_for_one_assignment_body(
        &mut self,
        stmt: &ForAxiomStmt,
        parameter_index_assignment: &Vec<usize>,
        param_value_strings_of_each_param: &Vec<Vec<String>>,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for (parameter_position, parameter_name) in stmt.params.iter().enumerate() {
            let assigned_integer_string = param_value_strings_of_each_param[parameter_position]
                [parameter_index_assignment[parameter_position]]
                .clone();
            self.store_identifier_obj(parameter_name)
                .map_err(RuntimeError::from)?;

            let parameter_in_z_atomic_fact = AtomicFact::InFact(crate::fact::InFact::new(
                Obj::Identifier(Identifier::new(parameter_name.clone())),
                Obj::StandardSet(StandardSet::Z),
                stmt.line_file.clone(),
            ));
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                parameter_in_z_atomic_fact,
            )
            .map_err(RuntimeError::from)?;

            let parameter_equal_to_assigned_obj_atomic_fact =
                AtomicFact::EqualFact(crate::fact::EqualFact::new(
                    Obj::Identifier(Identifier::new(parameter_name.clone())),
                    Obj::Number(Number::new(assigned_integer_string)),
                    stmt.line_file.clone(),
                ));
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                parameter_equal_to_assigned_obj_atomic_fact,
            )
            .map_err(RuntimeError::from)?;
        }

        let mut no_dom_fact_is_false = true;
        for dom_fact in stmt.dom_facts.iter() {
            let verify_dom_result =
                self.verify_atomic_fact(dom_fact, &VerifyState::new(0, false))?;
            if verify_dom_result.is_true() {
                self.store_atomic_fact_without_well_defined_verified_and_infer(dom_fact.clone())
                    .map_err(RuntimeError::from)?;
                inside_results.push(verify_dom_result);
            } else {
                let reversed = dom_fact.make_reversed();
                let verify_reversed_dom_result =
                    self.verify_atomic_fact(&reversed, &VerifyState::new(0, false))?;
                if verify_reversed_dom_result.is_unknown() {
                    return Err(RuntimeError::from(ExecStmtError::with_message_and_cause(
                        Stmt::ForAxiomStmt(stmt.clone()),
                        format!(
                            "by for: domain fact `{}` or its reversed `{}` must be verified to be true, but both are unknown",
                            dom_fact, reversed
                        ),
                        None,
                        inside_results,
                    )));
                }
                if verify_reversed_dom_result.is_true() {
                    no_dom_fact_is_false = false;
                }
            }
        }

        if !no_dom_fact_is_false {
            return Ok(inside_results);
        }

        for proof_stmt in stmt.proof.iter() {
            let proof_result = self.exec_stmt(proof_stmt)?;
            inside_results.push(proof_result);
        }
        for fact_to_prove in stmt.then_facts.iter() {
            let verified_result = self.verify_exist_or_and_chain_atomic_fact(
                fact_to_prove,
                &VerifyState::new(0, false),
            )?;
            if verified_result.is_unknown() {
                return Err(RuntimeError::from(
                    ExecStmtError::with_message_and_cause(
                        Stmt::ForAxiomStmt(stmt.clone()),
                        format!("by for: failed to prove `{}`", fact_to_prove),
                        None,
                        inside_results,
                    ),
                ));
            }
            inside_results.push(verified_result);
        }
        Ok(inside_results)
    }
}
