use crate::prelude::*;

impl Runtime {
    pub fn exec_witness_exist_fact(
        &mut self,
        stmt: &WitnessExistFact,
    ) -> Result<StmtResult, RuntimeError> {
        let witness_stmt = stmt.clone().into();

        let inside_results_when_verify = self.run_in_local_env(|rt| {
            let witness_stmt = stmt.clone().into();
            let verify_state_for_well_defined = VerifyState::new(0, false);

            let expected_param_count = stmt
                .exist_fact_in_witness
                .params_def_with_type
                .number_of_params();
            if expected_param_count != stmt.equal_tos.len() {
                return Err(RuntimeError::from(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        witness_stmt,
                        "witness exist fact: parameter count mismatch".to_string(),
                        None,
                        vec![],
                    ),
                ));
            }

            if let Err(well_defined_error) = rt.verify_exist_fact_well_defined(
                &stmt.exist_fact_in_witness,
                &verify_state_for_well_defined,
            ) {
                return Err(RuntimeError::from(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        witness_stmt,
                        "witness exist fact: exist fact well-defined failed".to_string(),
                        Some(well_defined_error.into()),
                        vec![],
                    ),
                ));
            }

            for equal_to_obj in stmt.equal_tos.iter() {
                if let Err(well_defined_error) = rt.verify_obj_well_defined_and_store_cache(
                    equal_to_obj,
                    &verify_state_for_well_defined,
                ) {
                    return Err(RuntimeError::from(
                        RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                            witness_stmt,
                            "witness exist fact: equal_to well-defined failed".to_string(),
                            Some(well_defined_error.into()),
                            vec![],
                        ),
                    ));
                }
            }

            let have_obj_equal_stmt = HaveObjEqualStmt {
                param_def: stmt.exist_fact_in_witness.params_def_with_type.clone(),
                objs_equal_to: stmt.equal_tos.clone(),
                line_file: stmt.line_file.clone(),
            };

            match rt.exec_have_obj_equal_stmt(&have_obj_equal_stmt) {
                Ok(_binding_result) => {}
                Err(exec_stmt_error) => {
                    return Err(RuntimeError::from(exec_stmt_error));
                }
            }

            let mut inside_results: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                match rt.exec_stmt(proof_stmt) {
                    Ok(proof_result) => {
                        inside_results.push(proof_result);
                    }
                    Err(proof_exec_error) => {
                        return Err(RuntimeError::from(
                            RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                                witness_stmt.clone(),
                                proof_stmt.to_string(),
                                Some(proof_exec_error),
                                inside_results,
                            ),
                        ));
                    }
                }
            }

            let param_to_obj_map = stmt
                .exist_fact_in_witness
                .params_def_with_type
                .param_defs_and_args_to_param_to_arg_map(stmt.equal_tos.as_slice());
            let instantiated_exist_fact =
                rt.inst_exist_fact(&stmt.exist_fact_in_witness, &param_to_obj_map)?;

            let verify_state_for_proof_check = VerifyState::new(0, false);
            for internal_fact_template in instantiated_exist_fact.facts.iter() {
                let internal_fact = internal_fact_template.clone().to_fact();
                let verification_result = rt
                    .verify_fact_return_err_if_not_true(&internal_fact, &verify_state_for_proof_check);
                if let Err(verify_error) = verification_result {
                    return Err(RuntimeError::from(verify_error));
                }
            }

            Ok(inside_results)
        });

        let inside_results = match inside_results_when_verify {
            Ok(proof_inside_results) => proof_inside_results,
            Err(inside_results_error) => return Err(RuntimeError::from(inside_results_error)),
        };

        // 6) Store exist fact into the top-level (big) environment.
        let store_result = self.store_fact_without_well_defined_verified_and_infer(
            stmt.exist_fact_in_witness.clone().into(),
        );
        match store_result {
            Ok(infer_result) => Ok((NonFactualStmtSuccess::new(witness_stmt, infer_result, inside_results)).into()),
            Err(store_error) => Err(RuntimeError::from(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    witness_stmt,
                    "witness exist fact: failed to store exist fact".to_string(),
                    Some(store_error.into()),
                    // Keep inside_results for error reporting.
                    inside_results,
                ),
            )),
        }
    }

    pub fn exec_witness_nonempty_set(
        &mut self,
        stmt: &WitnessNonemptySet,
    ) -> Result<StmtResult, RuntimeError> {
        let witness_stmt = stmt.clone().into();

        let inside_results_when_verify = self.run_in_local_env(|rt| {
            let witness_stmt = stmt.clone().into();

            let verify_state_for_well_defined = VerifyState::new(0, false);

            if let Err(well_defined_error) =
                rt.verify_obj_well_defined_and_store_cache(&stmt.obj, &verify_state_for_well_defined)
            {
                return Err(RuntimeError::from(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        witness_stmt,
                        "witness nonempty set: obj well-defined failed".to_string(),
                        Some(well_defined_error.into()),
                        vec![],
                    ),
                ));
            }

            if let Err(well_defined_error) =
                rt.verify_obj_well_defined_and_store_cache(&stmt.set, &verify_state_for_well_defined)
            {
                return Err(RuntimeError::from(
                    RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                        witness_stmt.clone(),
                        "witness nonempty set: set well-defined failed".to_string(),
                        Some(well_defined_error.into()),
                        vec![],
                    ),
                ));
            }

            let mut inside_results: Vec<StmtResult> = Vec::new();
            for proof_stmt in stmt.proof.iter() {
                match rt.exec_stmt(proof_stmt) {
                    Ok(proof_result) => {
                        inside_results.push(proof_result);
                    }
                    Err(proof_exec_error) => {
                        return Err(RuntimeError::from(
                            RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                                witness_stmt.clone(),
                                proof_stmt.to_string(),
                                Some(proof_exec_error),
                                inside_results,
                            ),
                        ));
                    }
                }
            }

            let verify_state_for_proof_check = VerifyState::new(0, false);
            if let Obj::FnSet(fn_set) = &stmt.set {
                let ret_nonempty_fact = IsNonemptySetFact::new(
                    fn_set.ret_set.as_ref().clone(),
                    stmt.line_file.clone(),
                ).into();
                let ret_check = rt.verify_non_equational_atomic_fact_with_builtin_rules(
                    &ret_nonempty_fact,
                    &verify_state_for_proof_check,
                )?;
                if ret_check.is_true() {
                    return Ok(inside_results);
                }
            }

            let membership_fact = InFact::new(
                stmt.obj.clone(),
                stmt.set.clone(),
                stmt.line_file.clone(),
            ).into();
            rt.verify_fact_return_err_if_not_true(&membership_fact, &verify_state_for_proof_check)?;

            Ok(inside_results)
        });

        let inside_results = match inside_results_when_verify {
            Ok(proof_inside_results) => proof_inside_results,
            Err(inside_results_error) => return Err(RuntimeError::from(inside_results_error)),
        };

        // 6) Store nonempty set fact into the top-level (big) environment.
        let store_result = self.store_fact_without_well_defined_verified_and_infer(
            IsNonemptySetFact::new(
                stmt.set.clone(),
                stmt.line_file.clone(),
            ).into(),
        );
        match store_result {
            Ok(infer_result) => Ok((NonFactualStmtSuccess::new(witness_stmt, infer_result, inside_results)).into()),
            Err(store_error) => Err(RuntimeError::from(
                RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                    witness_stmt,
                    "witness nonempty set: failed to store nonempty set fact".to_string(),
                    Some(store_error.into()),
                    // Keep inside_results for error reporting.
                    inside_results,
                ),
            )),
        }
    }
}
