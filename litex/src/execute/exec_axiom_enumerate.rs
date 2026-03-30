use crate::prelude::*;

impl Runtime {
    pub fn exec_enumerate_axiom_stmt(
        &mut self,
        stmt: &EnumerateAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let corresponding_forall_fact = stmt.to_corresponding_forall_fact().map_err(|msg| {
            RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                Stmt::EnumerateAxiomStmt(stmt.clone()),
                msg,
                None,
                vec![],
            ))
        })?;

        self.verify_fact_well_defined(&corresponding_forall_fact, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::EnumerateAxiomStmt(stmt.clone()),
                    format!(
                        "enumerate: corresponding forall `{}` is not well-defined",
                        corresponding_forall_fact
                    ),
                    Some(well_defined_error.into()),
                    vec![],
                ))
            })?;

        let enumerate_cartesian_product_is_empty = stmt
            .param_sets
            .iter()
            .any(|list_set_obj| list_set_obj.list.is_empty());
        if enumerate_cartesian_product_is_empty {
            let infer_result_from_stored_forall_fact = self
                .store_fact_without_well_defined_verified_and_infer(&corresponding_forall_fact)
                .map_err(|store_fact_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                        Stmt::EnumerateAxiomStmt(stmt.clone()),
                        format!(
                            "enumerate: failed to store corresponding forall `{}`",
                            corresponding_forall_fact
                        ),
                        Some(store_fact_error.into()),
                        vec![],
                    ))
                })?;
            return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(
                    Stmt::EnumerateAxiomStmt(stmt.clone()),
                    infer_result_from_stored_forall_fact,
                    vec![],
                ),
            ));
        }

        let mut all_inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        let mut current_parameter_index_assignment = Self::enumerate_start_index_assignment(stmt);
        loop {
            let mut one_assignment_inside_results = self
                .exec_enumerate_axiom_stmt_for_one_assignment(
                    stmt,
                    &current_parameter_index_assignment,
                )?;
            all_inside_results.append(&mut one_assignment_inside_results);
            let next_parameter_index_assignment =
                Self::enumerate_next_index_assignment(stmt, &current_parameter_index_assignment);
            match next_parameter_index_assignment {
                Some(next_parameter_index_assignment) => {
                    current_parameter_index_assignment = next_parameter_index_assignment;
                }
                None => break,
            }
        }

        let infer_result_from_stored_forall_fact = self
            .store_fact_without_well_defined_verified_and_infer(&corresponding_forall_fact)
            .map_err(|store_fact_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::EnumerateAxiomStmt(stmt.clone()),
                    format!(
                        "enumerate: failed to store corresponding forall `{}`",
                        corresponding_forall_fact
                    ),
                    Some(store_fact_error.into()),
                    vec![],
                ))
            })?;

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::EnumerateAxiomStmt(stmt.clone()),
                {
                    let mut infer_result = InferResult::new();
                    infer_result.new_fact(&corresponding_forall_fact);
                    infer_result.new_infer_result_inside(infer_result_from_stored_forall_fact);
                    infer_result
                },
                all_inside_results,
            ),
        ))
    }

    fn enumerate_start_index_assignment(stmt: &EnumerateAxiomStmt) -> Vec<usize> {
        let mut start_index_assignment: Vec<usize> = Vec::new();
        for _ in stmt.param_sets.iter() {
            start_index_assignment.push(0);
        }
        start_index_assignment
    }

    fn enumerate_next_index_assignment(
        stmt: &EnumerateAxiomStmt,
        current_parameter_index_assignment: &Vec<usize>,
    ) -> Option<Vec<usize>> {
        let mut next_parameter_index_assignment = current_parameter_index_assignment.clone();
        for reversed_position in 0..next_parameter_index_assignment.len() {
            let position_from_right = next_parameter_index_assignment.len() - 1 - reversed_position;
            let current_index = next_parameter_index_assignment[position_from_right];
            let current_list_set_length = stmt.param_sets[position_from_right].list.len();
            if current_index + 1 < current_list_set_length {
                next_parameter_index_assignment[position_from_right] = current_index + 1;
                return Some(next_parameter_index_assignment);
            }
            next_parameter_index_assignment[position_from_right] = 0;
        }
        None
    }

    fn exec_enumerate_axiom_stmt_for_one_assignment(
        &mut self,
        stmt: &EnumerateAxiomStmt,
        parameter_index_assignment: &Vec<usize>,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        self.push_env();
        let execute_result = self
            .exec_enumerate_axiom_stmt_for_one_assignment_body(stmt, parameter_index_assignment);
        self.pop_env();
        execute_result
    }

    fn exec_enumerate_axiom_stmt_for_one_assignment_body(
        &mut self,
        stmt: &EnumerateAxiomStmt,
        parameter_index_assignment: &Vec<usize>,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for (parameter_position, parameter_name) in stmt.params.iter().enumerate() {
            let assigned_obj = (*stmt.param_sets[parameter_position].list
                [parameter_index_assignment[parameter_position]])
                .clone();
            self.store_identifier_obj(parameter_name)
                .map_err(RuntimeError::from)?;
            let parameter_equal_to_assigned_obj_atomic_fact =
                AtomicFact::EqualFact(EqualFact::new(
                    Obj::Identifier(Identifier::new(parameter_name.clone())),
                    assigned_obj.clone(),
                    stmt.line_file,
                ));
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                &parameter_equal_to_assigned_obj_atomic_fact,
            )
            .map_err(RuntimeError::from)?;
        }

        for proof_stmt in stmt.proof.iter() {
            let proof_result = self.exec_stmt(proof_stmt)?;
            inside_results.push(proof_result);
        }

        for fact_to_prove in stmt.to_prove.iter() {
            let verified_result = self
                .verify_fact_return_err_if_not_true(fact_to_prove, &VerifyState::new(0, false))?;
            inside_results.push(verified_result);
        }
        Ok(inside_results)
    }
}
