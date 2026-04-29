use crate::prelude::*;

impl Runtime {
    pub fn exec_by_extension_stmt(
        &mut self,
        stmt: &ByExtensionStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.left, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                short_exec_error(
 stmt.clone().into(),
                    format!("by extension: left set `{}` is not well-defined", stmt.left),
                    Some(well_defined_error),
                    vec![],
                )
            })?;
        self.verify_obj_well_defined_and_store_cache(&stmt.right, &VerifyState::new(0, false))
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

        let local_proof_result: Result<(Vec<StmtResult>, Fact, Fact), RuntimeError> = self
            .run_in_local_env(|rt| {
                let mut inside_results: Vec<StmtResult> = Vec::new();
                for proof_stmt in stmt.proof.iter() {
                    let one_proof_stmt_exec_result =
                        rt.exec_stmt(proof_stmt).map_err(|stmt_error| {
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
                    inside_results.push(one_proof_stmt_exec_result);
                }

                let unused_name = rt.generate_random_unused_name();

                let left_to_right_forall_fact = ForallFact::new(
                    ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                        vec![unused_name.clone()],
                        ParamType::Obj(stmt.left.clone()),
                    )]),
                    vec![],
                    vec![InFact::new(
                        obj_for_bound_param_in_scope(unused_name.clone(), ParamObjType::Forall),
                        stmt.right.clone(),
                        stmt.line_file.clone(),
                    )
                    .into()],
                    stmt.line_file.clone(),
                )?
                .into();
                rt.verify_fact_return_err_if_not_true(
                    &left_to_right_forall_fact,
                    &VerifyState::new(0, false),
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
                })?;

                let right_to_left_forall_fact = ForallFact::new(
                    ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                        vec![unused_name.clone()],
                        ParamType::Obj(stmt.right.clone()),
                    )]),
                    vec![],
                    vec![InFact::new(
                        obj_for_bound_param_in_scope(unused_name.clone(), ParamObjType::Forall),
                        stmt.left.clone(),
                        stmt.line_file.clone(),
                    )
                    .into()],
                    stmt.line_file.clone(),
                )?
                .into();
                rt.verify_fact_return_err_if_not_true(
                    &right_to_left_forall_fact,
                    &VerifyState::new(0, false),
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
                })?;

                Ok::<_, RuntimeError>((
                    inside_results,
                    left_to_right_forall_fact,
                    right_to_left_forall_fact,
                ))
            });
        let local_proof_result = local_proof_result?;
        let (inside_results, _, _) = local_proof_result;

        let left_equal_to_right_atomic_fact = AtomicFact::EqualFact(EqualFact::new(
            stmt.left.clone(),
            stmt.right.clone(),
            stmt.line_file.clone(),
        ));

        let mut infer_result = InferResult::new();
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                left_equal_to_right_atomic_fact,
            )?,
        );

        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results)).into())
    }
}
