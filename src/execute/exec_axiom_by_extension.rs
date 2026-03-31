use crate::prelude::*;

impl Runtime {
    pub fn exec_by_extension_axiom_stmt(
        &mut self,
        stmt: &ByExtensionAxiomStmt,
    ) -> Result<NonErrStmtExecResult, RuntimeError> {
        self.verify_obj_well_defined_and_store_cache(&stmt.left, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByExtensionAxiomStmt(stmt.clone()),
                    format!("by extension: left set `{}` is not well-defined", stmt.left),
                    Some(well_defined_error.into()),
                    vec![],
                ))
            })?;
        self.verify_obj_well_defined_and_store_cache(&stmt.right, &VerifyState::new(0, false))
            .map_err(|well_defined_error| {
                RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                    Stmt::ByExtensionAxiomStmt(stmt.clone()),
                    format!(
                        "by extension: right set `{}` is not well-defined",
                        stmt.right
                    ),
                    Some(well_defined_error.into()),
                    vec![],
                ))
            })?;

        self.push_env();
        let local_proof_result =
            (|| -> Result<(Vec<NonErrStmtExecResult>, Fact, Fact), RuntimeError> {
                let mut inside_results: Vec<NonErrStmtExecResult> = Vec::new();
                for proof_stmt in stmt.proof.iter() {
                    let one_proof_stmt_exec_result =
                        self.exec_stmt(proof_stmt).map_err(|stmt_error| {
                            RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                                Stmt::ByExtensionAxiomStmt(stmt.clone()),
                                format!(
                                    "by extension: failed to execute proof stmt `{}`",
                                    proof_stmt
                                ),
                                Some(stmt_error),
                                vec![],
                            ))
                        })?;
                    inside_results.push(one_proof_stmt_exec_result);
                }

                let unused_name = self.generate_a_random_unused_name();

                let left_to_right_forall_fact = Fact::ForallFact(ForallFact::new(
                    vec![ParamDefWithParamType(
                        vec![unused_name.clone()],
                        ParamType::Obj(stmt.left.clone()),
                    )],
                    vec![],
                    vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                        InFact::new(
                            Obj::Identifier(Identifier::new(unused_name.clone())),
                            stmt.right.clone(),
                            stmt.line_file,
                        ),
                    ))],
                    stmt.line_file,
                ));
                self.verify_fact_return_err_if_not_true(
                    &left_to_right_forall_fact,
                    &VerifyState::new(0, false),
                )
                .map_err(|verify_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                        Stmt::ByExtensionAxiomStmt(stmt.clone()),
                        format!(
                            "by extension: failed to prove left subset right `{}`",
                            left_to_right_forall_fact
                        ),
                        Some(verify_error.into()),
                        vec![],
                    ))
                })?;

                let right_to_left_forall_fact = Fact::ForallFact(ForallFact::new(
                    vec![ParamDefWithParamType(
                        vec![unused_name.clone()],
                        ParamType::Obj(stmt.right.clone()),
                    )],
                    vec![],
                    vec![ExistOrAndChainAtomicFact::AtomicFact(AtomicFact::InFact(
                        InFact::new(
                            Obj::Identifier(Identifier::new(unused_name.clone())),
                            stmt.left.clone(),
                            stmt.line_file,
                        ),
                    ))],
                    stmt.line_file,
                ));
                self.verify_fact_return_err_if_not_true(
                    &right_to_left_forall_fact,
                    &VerifyState::new(0, false),
                )
                .map_err(|verify_error| {
                    RuntimeError::ExecStmtError(ExecStmtError::with_message_and_cause(
                        Stmt::ByExtensionAxiomStmt(stmt.clone()),
                        format!(
                            "by extension: failed to prove right subset left `{}`",
                            right_to_left_forall_fact
                        ),
                        Some(verify_error.into()),
                        vec![],
                    ))
                })?;
                Ok((
                    inside_results,
                    left_to_right_forall_fact,
                    right_to_left_forall_fact,
                ))
            })();
        self.pop_env();
        let (inside_results, _, _) = local_proof_result?;

        let left_equal_to_right_atomic_fact = AtomicFact::EqualFact(crate::fact::EqualFact::new(
            stmt.left.clone(),
            stmt.right.clone(),
            stmt.line_file,
        ));

        let mut infer_result = InferResult::new();
        infer_result.new_infer_result_inside(
            self.store_atomic_fact_without_well_defined_verified_and_infer(
                left_equal_to_right_atomic_fact,
            )?,
        );

        Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
            NonFactualStmtSuccess::new(
                Stmt::ByExtensionAxiomStmt(stmt.clone()),
                infer_result,
                inside_results,
            ),
        ))
    }
}
