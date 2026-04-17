use crate::prelude::*;

impl Runtime {
    pub fn exec_by_enumerate_stmt(
        &mut self,
        stmt: &ByEnumerateStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let (params, param_sets) = stmt.expanded_list_set_params().map_err(|msg| {
            short_exec_error(stmt.clone().into(), msg, None, vec![])
        })?;

        let corresponding_forall_fact = stmt.to_corresponding_forall_fact().map_err(|msg| {
            short_exec_error(stmt.clone().into(), msg, None, vec![])
        })?;

        self.verify_forall_fact_params_and_dom_well_defined(
            &stmt.forall_fact,
            &VerifyState::new(0, false),
        )
        .map_err(|well_defined_error| {
            short_exec_error(
                stmt.clone().into(),
                format!(
                    "by enumerate: forall parameters or domain is not well-defined (`{}`)",
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
                .store_fact_without_well_defined_verified_and_infer(
                    corresponding_forall_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by enumerate: failed to store corresponding forall `{}`",
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
            return Ok(
                (NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![])).into(),
            );
        }

        let mut current_parameter_index_assignment =
            Self::by_enumerate_start_index_assignment(&param_sets);
        loop {
            self.exec_by_enumerate_stmt_for_one_assignment(
                stmt,
                &params,
                &param_sets,
                &current_parameter_index_assignment,
            )?;
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
            .store_fact_without_well_defined_verified_and_infer(corresponding_forall_fact.clone())
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by enumerate: failed to store corresponding forall `{}`",
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

        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![])).into())
    }

    fn infer_result_with_generated_forall_and_store_infer(
        generated_forall_fact: &Fact,
        infer_after_store: InferResult,
    ) -> InferResult {
        let mut infer_result = InferResult::new();
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
        stmt: &ByEnumerateStmt,
        params: &[String],
        param_sets: &[ListSet],
        parameter_index_assignment: &Vec<usize>,
    ) -> Result<(), RuntimeError> {
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
        stmt: &ByEnumerateStmt,
        params: &[String],
        param_sets: &[ListSet],
        parameter_index_assignment: &Vec<usize>,
    ) -> Result<(), RuntimeError> {
        for (parameter_position, parameter_name) in params.iter().enumerate() {
            let assigned_obj = (*param_sets[parameter_position].list
                [parameter_index_assignment[parameter_position]])
                .clone();
            self.store_identifier_obj(parameter_name)?;
            let parameter_equal_to_assigned_obj_atomic_fact = EqualFact::new(
                parameter_name.to_string().into(),
                assigned_obj,
                stmt.line_file.clone(),
            )
            .into();
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                parameter_equal_to_assigned_obj_atomic_fact,
            )?;
        }

        let verify_state = VerifyState::new(0, false);
        for dom_fact in stmt.forall_fact.dom_facts.iter() {
            let verify_dom_result = self.verify_fact(dom_fact, &verify_state)?;
            if verify_dom_result.is_true() {
                self.store_fact_without_well_defined_verified_and_infer(dom_fact.clone())?;
            } else if verify_dom_result.is_unknown() {
                if let Some(negated_domain) = Self::negated_domain_fact_for_by_for_skip(dom_fact) {
                    let verify_negation_result =
                        self.verify_fact(&negated_domain, &verify_state)?;
                    if verify_negation_result.is_true() {
                        return Ok(());
                    }
                }
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by enumerate: domain fact `{}` is not decided (could not verify it or its negation)",
                        dom_fact
                    ),
                    None,
                    vec![],
                ));
            }
        }

        for proof_stmt in stmt.proof.iter() {
            self.exec_stmt(proof_stmt)?;
        }
        for fact_to_prove in stmt.forall_fact.then_facts.iter() {
            let verified_result =
                self.verify_exist_or_and_chain_atomic_fact(fact_to_prove, &verify_state)?;
            if verified_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!("by enumerate: failed to prove `{}`", fact_to_prove),
                    None,
                    vec![],
                ));
            }
        }
        Ok(())
    }
}
