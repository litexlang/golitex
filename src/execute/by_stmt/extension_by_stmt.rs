use crate::prelude::*;

impl Runtime {
    pub fn exec_by_extension_stmt(
        &mut self,
        stmt: &ByExtensionStmt,
    ) -> Result<StmtResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.left, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::ExecStmtError({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message =
                        format!("by extension: left set `{}` is not well-defined", stmt.left);
                    let __cause = Some(well_defined_error);
                    let __inside = vec![];
                    let __line_file = __stmt.line_file();
                    let __previous_error = if __message.is_empty() {
                        __cause
                    } else {
                        Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                    };
                    RuntimeErrorStruct::new(
                        Some(__stmt),
                        __message,
                        __line_file,
                        __previous_error,
                        __inside,
                    )
                })
            })?;
        self.verify_obj_well_defined_and_store_cache(&stmt.right, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::ExecStmtError({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message = format!(
                        "by extension: right set `{}` is not well-defined",
                        stmt.right
                    );
                    let __cause = Some(well_defined_error);
                    let __inside = vec![];
                    let __line_file = __stmt.line_file();
                    let __previous_error = if __message.is_empty() {
                        __cause
                    } else {
                        Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                    };
                    RuntimeErrorStruct::new(
                        Some(__stmt),
                        __message,
                        __line_file,
                        __previous_error,
                        __inside,
                    )
                })
            })?;

        let local_proof_result: Result<(Vec<StmtResult>, Fact, Fact), RuntimeError> = self
            .run_in_local_env(|rt| {
                let mut inside_results: Vec<StmtResult> = Vec::new();
                for proof_stmt in stmt.proof.iter() {
                    let one_proof_stmt_exec_result =
                        rt.exec_stmt(proof_stmt).map_err(|stmt_error| {
                            RuntimeError::ExecStmtError({
                                let __stmt: Stmt = stmt.clone().into();
                                let __message = format!(
                                    "by extension: failed to execute proof stmt `{}`",
                                    proof_stmt
                                );
                                let __cause = Some(stmt_error);
                                let __inside = vec![];
                                let __line_file = __stmt.line_file();
                                let __previous_error = if __message.is_empty() {
                                    __cause
                                } else {
                                    Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                                };
                                RuntimeErrorStruct::new(
                                    Some(__stmt),
                                    __message,
                                    __line_file,
                                    __previous_error,
                                    __inside,
                                )
                            })
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
                        unused_name.clone().into(),
                        stmt.right.clone(),
                        stmt.line_file.clone(),
                    )
                    .into()],
                    stmt.line_file.clone(),
                )
                .into();
                rt.verify_fact_return_err_if_not_true(
                    &left_to_right_forall_fact,
                    &VerifyState::new(0, false),
                )
                .map_err(|verify_error| {
                    RuntimeError::ExecStmtError({
                        let __stmt: Stmt = stmt.clone().into();
                        let __message = format!(
                            "by extension: failed to prove left subset right `{}`",
                            left_to_right_forall_fact
                        );
                        let __cause = Some(verify_error);
                        let __inside = vec![];
                        let __line_file = __stmt.line_file();
                        let __previous_error = if __message.is_empty() {
                            __cause
                        } else {
                            Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                        };
                        RuntimeErrorStruct::new(
                            Some(__stmt),
                            __message,
                            __line_file,
                            __previous_error,
                            __inside,
                        )
                    })
                })?;

                let right_to_left_forall_fact = ForallFact::new(
                    ParamDefWithType::new(vec![ParamGroupWithParamType::new(
                        vec![unused_name.clone()],
                        ParamType::Obj(stmt.right.clone()),
                    )]),
                    vec![],
                    vec![InFact::new(
                        unused_name.clone().into(),
                        stmt.left.clone(),
                        stmt.line_file.clone(),
                    )
                    .into()],
                    stmt.line_file.clone(),
                )
                .into();
                rt.verify_fact_return_err_if_not_true(
                    &right_to_left_forall_fact,
                    &VerifyState::new(0, false),
                )
                .map_err(|verify_error| {
                    RuntimeError::ExecStmtError({
                        let __stmt: Stmt = stmt.clone().into();
                        let __message = format!(
                            "by extension: failed to prove right subset left `{}`",
                            right_to_left_forall_fact
                        );
                        let __cause = Some(verify_error);
                        let __inside = vec![];
                        let __line_file = __stmt.line_file();
                        let __previous_error = if __message.is_empty() {
                            __cause
                        } else {
                            Some(
                    UnknownRuntimeError(RuntimeErrorStruct::new(
                Some(__stmt.clone()),
                __message.clone(),
                __line_file.clone(),
                __cause,
                vec![],
            ))
            .into(),
                )
                        };
                        RuntimeErrorStruct::new(
                            Some(__stmt),
                            __message,
                            __line_file,
                            __previous_error,
                            __inside,
                        )
                    })
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
