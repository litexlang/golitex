use crate::prelude::*;

impl Runtime {
    pub fn exec_witness_exist_fact(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let witness_stmt = Stmt::WitnessExistFact(stmt.clone());

        self.push_env();

        let inside_results_when_verify = self.exec_witness_exist_fact_body(stmt);

        // End verification: pop local environment.
        self.pop_env();

        let inside_results = match inside_results_when_verify {
            Ok(proof_inside_results) => proof_inside_results,
            Err(inside_results_error) => return Err(RuntimeError::from(inside_results_error)),
        };

        // 6) Store exist fact into the top-level (big) environment.
        let store_result = self.store_fact_without_well_defined_verified_and_infer(
            Fact::ExistFact(stmt.exist_fact_in_witness.clone()),
        );
        match store_result {
            Ok(infer_result) => Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(witness_stmt, infer_result, inside_results),
            )),
            Err(store_error) => Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    witness_stmt,
                    "witness exist fact: failed to store exist fact".to_string(),
                    Some(store_error.into()),
                    // Keep inside_results for error reporting.
                    inside_results,
                ),
            )),
        }
    }

    fn exec_witness_exist_fact_body(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        let witness_stmt = Stmt::WitnessExistFact(stmt.clone());
        let verify_state_for_well_defined = VerifyState::new(0, false);

        let expected_param_count = ParamDefWithParamType::number_of_params(
            &stmt.exist_fact_in_witness.params_def_with_type,
        );
        if expected_param_count != stmt.equal_tos.len() {
            return Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    witness_stmt,
                    "witness exist fact: parameter count mismatch".to_string(),
                    None,
                    vec![],
                ),
            ));
        }

        // 1) Verify exist fact is well-defined.
        if let Err(well_defined_error) = self.verify_exist_fact_well_defined(
            &stmt.exist_fact_in_witness,
            &verify_state_for_well_defined,
        ) {
            return Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    witness_stmt,
                    "witness exist fact: exist fact well-defined failed".to_string(),
                    Some(well_defined_error.into()),
                    vec![],
                ),
            ));
        }

        // 2) Verify each provided equal_to object is well-defined.
        for equal_to_obj in stmt.equal_tos.iter() {
            if let Err(well_defined_error) = self.verify_obj_well_defined_and_store_cache(
                equal_to_obj,
                &verify_state_for_well_defined,
            ) {
                return Err(RuntimeError::ExecStmtError(
                    ExecStmtError::with_message_and_cause(
                        witness_stmt,
                        "witness exist fact: equal_to well-defined failed".to_string(),
                        Some(well_defined_error.into()),
                        vec![],
                    ),
                ));
            }
        }

        // 3) Substitute equal_tos into exist's param_def and bind params.
        let have_obj_equal_stmt = HaveObjEqualStmt {
            param_def: stmt.exist_fact_in_witness.params_def_with_type.clone(),
            objs_equal_to: stmt.equal_tos.clone(),
            line_file: stmt.line_file,
        };

        match self.have_obj_equal_stmt(&have_obj_equal_stmt) {
            Ok(_binding_result) => {}
            Err(exec_stmt_error) => {
                return Err(RuntimeError::from(exec_stmt_error));
            }
        }

        // 4) Run witness proof in the local environment.
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for proof_stmt in stmt.proof.iter() {
            match self.exec_stmt(proof_stmt) {
                Ok(proof_result) => {
                    inside_results.push(proof_result);
                }
                Err(proof_exec_error) => {
                    return Err(RuntimeError::ExecStmtError(
                        ExecStmtError::with_message_and_cause(
                            witness_stmt.clone(),
                            proof_stmt.to_string(),
                            Some(proof_exec_error),
                            inside_results,
                        ),
                    ));
                }
            }
        }

        // 5) Substitute equal_tos into exist_fact_in_witness and check internal facts.
        let param_to_obj_map = ParamDefWithParamType::param_defs_and_args_to_param_to_arg_map(
            &stmt.exist_fact_in_witness.params_def_with_type,
            &stmt.equal_tos,
        );
        let instantiated_exist_fact = stmt.exist_fact_in_witness.instantiate(&param_to_obj_map);

        let verify_state_for_proof_check = VerifyState::new(0, false);
        for internal_fact_template in instantiated_exist_fact.facts.iter() {
            let internal_fact = internal_fact_template.clone().to_fact();
            let verification_result = self
                .verify_fact_return_err_if_not_true(&internal_fact, &verify_state_for_proof_check);
            if let Err(verify_error) = verification_result {
                return Err(RuntimeError::from(verify_error));
            }
        }

        Ok(inside_results)
    }

    pub fn exec_witness_nonempty_set(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        let witness_stmt = Stmt::WitnessNonemptySet(stmt.clone());

        self.push_env();

        let inside_results_when_verify = self.exec_witness_nonempty_set_body(stmt);

        // End verification: pop local environment.
        self.pop_env();

        let inside_results = match inside_results_when_verify {
            Ok(proof_inside_results) => proof_inside_results,
            Err(inside_results_error) => return Err(RuntimeError::from(inside_results_error)),
        };

        // 6) Store nonempty set fact into the top-level (big) environment.
        let store_result = self.store_fact_without_well_defined_verified_and_infer(
            Fact::AtomicFact(AtomicFact::IsNonemptySetFact(IsNonemptySetFact::new(
                stmt.set.clone(),
                stmt.line_file,
            ))),
        );
        match store_result {
            Ok(infer_result) => Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(witness_stmt, infer_result, inside_results),
            )),
            Err(store_error) => Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    witness_stmt,
                    "witness nonempty set: failed to store nonempty set fact".to_string(),
                    Some(store_error.into()),
                    // Keep inside_results for error reporting.
                    inside_results,
                ),
            )),
        }
    }

    fn exec_witness_nonempty_set_body(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<Vec<NonErrStmtExecResult>, RuntimeError> {
        let witness_stmt = Stmt::WitnessNonemptySet(stmt.clone());

        let verify_state_for_well_defined = VerifyState::new(0, false);

        if let Err(well_defined_error) =
            self.verify_obj_well_defined_and_store_cache(&stmt.obj, &verify_state_for_well_defined)
        {
            return Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    witness_stmt,
                    "witness nonempty set: obj well-defined failed".to_string(),
                    Some(well_defined_error.into()),
                    vec![],
                ),
            ));
        }

        if let Err(well_defined_error) =
            self.verify_obj_well_defined_and_store_cache(&stmt.set, &verify_state_for_well_defined)
        {
            return Err(RuntimeError::ExecStmtError(
                ExecStmtError::with_message_and_cause(
                    witness_stmt.clone(),
                    "witness nonempty set: set well-defined failed".to_string(),
                    Some(well_defined_error.into()),
                    vec![],
                ),
            ));
        }

        // 2) Run witness proof in the local environment.
        let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
        for proof_stmt in stmt.proof.iter() {
            match self.exec_stmt(proof_stmt) {
                Ok(proof_result) => {
                    inside_results.push(proof_result);
                }
                Err(proof_exec_error) => {
                    return Err(RuntimeError::ExecStmtError(
                        ExecStmtError::with_message_and_cause(
                            witness_stmt.clone(),
                            proof_stmt.to_string(),
                            Some(proof_exec_error),
                            inside_results,
                        ),
                    ));
                }
            }
        }

        // 3) Verify internal membership fact: `obj in set` must be true under the proof.
        let membership_fact = Fact::AtomicFact(AtomicFact::InFact(InFact::new(
            stmt.obj.clone(),
            stmt.set.clone(),
            stmt.line_file,
        )));
        let verify_state_for_proof_check = VerifyState::new(0, false);
        self.verify_fact_return_err_if_not_true(&membership_fact, &verify_state_for_proof_check)?;

        Ok(inside_results)
    }
}
