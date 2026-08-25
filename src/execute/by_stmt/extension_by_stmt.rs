use crate::prelude::*;

impl Runtime {
    pub fn exec_by_extension_stmt(
        &mut self,
        stmt: &ByExtensionStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.left, &ProofSearchState::initial())
            .map_err(|well_defined_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by extension: left set `{}` is not well-defined", stmt.left),
                    Some(well_defined_error),
                    vec![],
                )
            })?;
        self.verify_obj_well_defined_and_store_cache(&stmt.right, &ProofSearchState::initial())
            .map_err(|well_defined_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by extension: right set `{}` is not well-defined",
                        stmt.right
                    ),
                    Some(well_defined_error),
                    vec![],
                )
            })?;

        let local_proof_result: Result<(Vec<StmtResult>, StmtResult, StmtResult), RuntimeError> =
            self.run_in_local_env(|rt| {
                let mut proof_steps: Vec<StmtResult> = Vec::new();
                for proof_stmt in stmt.proof.iter() {
                    let one_proof_stmt_exec_result =
                        rt.execute_statement(proof_stmt).map_err(|stmt_error| {
                            short_exec_error(
                                stmt.clone().into(),
                                format!(
                                    "by extension: failed to execute proof stmt `{}`",
                                    proof_stmt
                                ),
                                Some(stmt_error),
                                vec![],
                            )
                        })?;
                    proof_steps.push(one_proof_stmt_exec_result);
                }

                let unused_name = rt.generate_random_unused_name();

                let left_to_right_subset_fact: AtomicFact = SubsetFact::new(
                    stmt.left.clone(),
                    stmt.right.clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let left_to_right_subset_result = rt.verify_atomic_fact_restricted_known_builtin(
                    &left_to_right_subset_fact,
                    &ProofSearchState::initial(),
                )?;

                let left_to_right_param = rt.fresh_param_group_with_type(
                    vec![unused_name.clone()],
                    ParamType::Obj(stmt.left.clone()),
                )?;
                let left_to_right_forall_fact = ForallFact::new_canonical_forall(
                    ParamDefWithType::new(vec![left_to_right_param.clone()]),
                    vec![],
                    vec![InFact::new(
                        obj_for_bound_param_in_scope(&left_to_right_param.params[0]),
                        stmt.right.clone(),
                        stmt.line_file.clone(),
                    )
                    .into()],
                    stmt.line_file.clone(),
                )?
                .into();
                let left_to_right_result = if left_to_right_subset_result.is_success() {
                    left_to_right_subset_result
                } else {
                    rt.verify_fact_or_error(
                        &left_to_right_forall_fact,
                        &ProofSearchState::initial(),
                    )
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "by extension: failed to prove left subset right `{}`",
                                left_to_right_forall_fact
                            ),
                            Some(verify_error),
                            vec![],
                        )
                    })?
                };

                let right_to_left_subset_fact: AtomicFact = SubsetFact::new(
                    stmt.right.clone(),
                    stmt.left.clone(),
                    stmt.line_file.clone(),
                )
                .into();
                let right_to_left_subset_result = rt.verify_atomic_fact_restricted_known_builtin(
                    &right_to_left_subset_fact,
                    &ProofSearchState::initial(),
                )?;

                let right_to_left_param = rt.fresh_param_group_with_type(
                    vec![unused_name.clone()],
                    ParamType::Obj(stmt.right.clone()),
                )?;
                let right_to_left_forall_fact = ForallFact::new_canonical_forall(
                    ParamDefWithType::new(vec![right_to_left_param.clone()]),
                    vec![],
                    vec![InFact::new(
                        obj_for_bound_param_in_scope(&right_to_left_param.params[0]),
                        stmt.left.clone(),
                        stmt.line_file.clone(),
                    )
                    .into()],
                    stmt.line_file.clone(),
                )?
                .into();
                let right_to_left_result = if right_to_left_subset_result.is_success() {
                    right_to_left_subset_result
                } else {
                    rt.verify_fact_or_error(
                        &right_to_left_forall_fact,
                        &ProofSearchState::initial(),
                    )
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "by extension: failed to prove right subset left `{}`",
                                right_to_left_forall_fact
                            ),
                            Some(verify_error),
                            vec![],
                        )
                    })?
                };
                Ok::<_, RuntimeError>((proof_steps, left_to_right_result, right_to_left_result))
            });
        let (proof_steps, left_to_right_check, right_to_left_check) = local_proof_result?;

        let left_equal_to_right_atomic_fact = AtomicFact::EqualFact(EqualFact::new(
            stmt.left.clone(),
            stmt.right.clone(),
            stmt.line_file.clone(),
        ));
        let prove_goal = left_equal_to_right_atomic_fact.to_string();

        let mut infer_result = SuccessInferResult::new();
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                left_equal_to_right_atomic_fact,
            )?,
        );

        let left_to_right_param = self.fresh_param_group_with_type(
            vec!["x".to_string()],
            ParamType::Obj(stmt.left.clone()),
        )?;
        let left_to_right_subset = ForallFact::new_canonical_forall(
            ParamDefWithType::new(vec![left_to_right_param.clone()]),
            vec![],
            vec![InFact::new(
                obj_for_bound_param_in_scope(&left_to_right_param.params[0]),
                stmt.right.clone(),
                stmt.line_file.clone(),
            )
            .into()],
            stmt.line_file.clone(),
        )?
        .to_string();
        let right_to_left_param = self.fresh_param_group_with_type(
            vec!["x".to_string()],
            ParamType::Obj(stmt.right.clone()),
        )?;
        let right_to_left_subset = ForallFact::new_canonical_forall(
            ParamDefWithType::new(vec![right_to_left_param.clone()]),
            vec![],
            vec![InFact::new(
                obj_for_bound_param_in_scope(&right_to_left_param.params[0]),
                stmt.left.clone(),
                stmt.line_file.clone(),
            )
            .into()],
            stmt.line_file.clone(),
        )?
        .to_string();
        let by_verification = SuccessVerifyByExtensionResult::new(
            stmt.left.to_string(),
            stmt.right.to_string(),
            prove_goal,
            left_to_right_subset,
            right_to_left_subset,
            proof_steps,
            left_to_right_check,
            right_to_left_check,
        );

        Ok(
            SuccessByStmtResult::ByExtensionStmt(Box::new(SuccessByExtensionStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: Some(by_verification),
            }))
            .into(),
        )
    }

    pub fn exec_by_extension_stmt_affect_environment_only(
        &mut self,
        stmt: &ByExtensionStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let equality_fact: Fact = EqualFact::new(
            stmt.left.clone(),
            stmt.right.clone(),
            stmt.line_file.clone(),
        )
        .into();
        let infer_result = self.store_trusted_fact_and_infer_with_reason(
            equality_fact,
            InferReason::VerifiedStatement,
        )?;
        Ok(
            SuccessByStmtResult::ByExtensionStmt(Box::new(SuccessByExtensionStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: None,
            }))
            .into(),
        )
    }
}
