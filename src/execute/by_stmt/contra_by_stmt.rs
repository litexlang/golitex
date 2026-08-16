use super::helpers_by_stmt::impossible_proof_error_message;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_contra_stmt(&mut self, stmt: &ByContraStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_by_contra_stmt_verify_well_definedness(stmt)?;
        let result = self.exec_by_contra_stmt_verify_process(stmt)?;
        let infer_result = self.exec_by_contra_stmt_affect_environment(stmt)?;

        Ok(result.with_infers(infer_result))
    }

    /// Mathematical contract: contradiction proof begins only from a
    /// well-defined target fact; the proof phase separately requires a
    /// supported logical negation and derives an explicit contradiction.
    fn exec_by_contra_stmt_verify_well_definedness(
        &mut self,
        stmt: &ByContraStmt,
    ) -> Result<(), RuntimeError> {
        let to_prove_fact = stmt.to_prove.clone();
        self.verify_fact_well_defined(&to_prove_fact, &UseContextVerifyState::new(0, false))
            .map_err(|verify_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by contra: failed to prove `{}`", to_prove_fact),
                    Some(verify_error),
                    vec![],
                )
            })
    }

    fn exec_by_contra_stmt_verify_process(
        &mut self,
        stmt: &ByContraStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let to_prove_fact = stmt.to_prove.clone();
        let (exec_proof_inside_results, last_error, reverse_assumption_fact_id, proof_scope) = self
            .run_in_local_env(|rt| {
                let captures_well_definedness = rt.captures_litex_to_lean_well_definedness();
                if captures_well_definedness {
                    rt.begin_statement_well_definedness_capture();
                }
                let proof_result =
                    rt.exec_by_contra_stmt_in_local_proof_scope(stmt, &to_prove_fact);
                match proof_result {
                    Ok((inside_results, last_error, fact_id, assumption_infers)) => {
                        let well_definedness = if captures_well_definedness {
                            rt.end_statement_well_definedness_capture()?
                        } else {
                            WellDefinednessCertificate::default()
                        };
                        Ok((
                            inside_results,
                            last_error,
                            fact_id,
                            LocalProofScopeVerificationResult::new(
                                assumption_infers,
                                Vec::new(),
                                well_definedness,
                            ),
                        ))
                    }
                    Err(error) => {
                        if captures_well_definedness {
                            rt.discard_statement_well_definedness_capture();
                        }
                        Err(error)
                    }
                }
            })?;

        if let Some(last_error) = last_error {
            return Err(short_exec_error(
                stmt.clone().into(),
                "by contra: failed to execute proof".to_string(),
                Some(last_error),
                exec_proof_inside_results,
            ));
        }

        let negated_assumption = logical_negation_for_by_contra(&stmt.to_prove)?;
        let by_verification = ByContraVerificationResult::new(
            stmt.to_prove.clone(),
            negated_assumption,
            reverse_assumption_fact_id,
            stmt.proof.len(),
            proof_scope,
            stmt.impossible_fact.clone(),
        )
        .into();

        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            InferResult::new(),
            exec_proof_inside_results,
            by_verification,
        )
        .into())
    }

    fn exec_by_contra_stmt_in_local_proof_scope(
        &mut self,
        stmt: &ByContraStmt,
        to_prove_fact: &Fact,
    ) -> Result<(Vec<StmtResult>, Option<RuntimeError>, FactId, InferResult), RuntimeError> {
        let mut inside_results: Vec<StmtResult> = Vec::new();
        let negated_to_prove_fact = logical_negation_for_by_contra(to_prove_fact)?;
        let mut assumption_infers = self
            .store_with_well_defined_verification_and_infer_with_default_verify_state(
                negated_to_prove_fact.clone(),
            )
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by contra: failed to store logical negation of `{}`",
                        to_prove_fact
                    ),
                    Some(store_fact_error),
                    vec![],
                )
            })?;
        self.attach_known_fact_ids_to_infer_result(&mut assumption_infers)?;
        let reverse_assumption_fact_id = self
            .known_fact_id_for_fact(&negated_to_prove_fact)?
            .ok_or_else(|| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by contra: reverse assumption `{}` has no FactId",
                        negated_to_prove_fact
                    ),
                    None,
                    vec![],
                )
            })?;

        let mut last_error: Option<RuntimeError> = None;
        for proof_stmt in stmt.proof.iter() {
            match self.exec_stmt(proof_stmt) {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    last_error = Some(statement_error);
                    break;
                }
            }
        }
        if last_error.is_some() {
            return Ok((
                inside_results,
                last_error,
                reverse_assumption_fact_id,
                assumption_infers,
            ));
        }

        let verify_impossible_fact_result =
            self.verify_atomic_fact(&stmt.impossible_fact, &UseContextVerifyState::new(0, false))?;
        if verify_impossible_fact_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                impossible_proof_error_message(&stmt.impossible_fact, None),
                None,
                inside_results,
            ));
        }

        let negated_impossible_fact = stmt.impossible_fact.logical_negation()?;
        let verify_negated_impossible_fact_result = self.verify_atomic_fact(
            &negated_impossible_fact,
            &UseContextVerifyState::new(0, false),
        )?;
        if verify_negated_impossible_fact_result.is_unknown() {
            return Err(short_exec_error(
                stmt.clone().into(),
                impossible_proof_error_message(&stmt.impossible_fact, None),
                None,
                vec![],
            ));
        }
        inside_results.push(verify_impossible_fact_result);
        inside_results.push(verify_negated_impossible_fact_result);

        Ok((
            inside_results,
            last_error,
            reverse_assumption_fact_id,
            assumption_infers,
        ))
    }

    pub(crate) fn exec_by_contra_stmt_affect_environment(
        &mut self,
        stmt: &ByContraStmt,
    ) -> Result<InferResult, RuntimeError> {
        let to_prove_fact = stmt.to_prove.clone();
        let to_prove_fact_display_string = to_prove_fact.to_string();
        if self.current_execution_is_trusted_file() {
            return self.store_trusted_fact_and_infer_with_reason(
                to_prove_fact,
                InferReason::VerifiedStatement,
            );
        }
        self.store_with_well_defined_verification_and_infer_with_default_verify_state(to_prove_fact)
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by contra: failed to release `{}`",
                        to_prove_fact_display_string
                    ),
                    Some(store_fact_error),
                    vec![],
                )
            })
    }

    pub(crate) fn exec_by_contra_stmt_affect_environment_only(
        &mut self,
        stmt: &ByContraStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_by_contra_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }
}

fn logical_negation_for_by_contra(fact: &Fact) -> Result<Fact, RuntimeError> {
    match fact {
        Fact::AtomicFact(atomic_fact) => Ok(atomic_fact.logical_negation()?.into()),
        Fact::ForallFact(forall_fact) => Ok(NotForallFact::new(forall_fact.clone()).into()),
        Fact::NotForall(not_forall) => Ok(not_forall.forall_fact.clone().into()),
        Fact::ExistFact(exist_fact) => match exist_fact {
            ExistFactEnum::ExistFact(body) => Ok(ExistFactEnum::NotExistFact(body.clone()).into()),
            ExistFactEnum::NotExistFact(body) => Ok(ExistFactEnum::ExistFact(body.clone()).into()),
            ExistFactEnum::ExistUniqueFact(_) => Err(RuntimeError::ExecStmtError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "by contra: cannot build logical negation for `{}` yet",
                        fact
                    ),
                    fact.line_file(),
                ),
            )),
        },
        Fact::OrFact(_) | Fact::AndFact(_) | Fact::ChainFact(_) | Fact::ForallFactWithIff(_) => {
            Err(RuntimeError::ExecStmtError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "by contra: cannot build logical negation for `{}` yet",
                        fact
                    ),
                    fact.line_file(),
                ),
            ))
        }
    }
}
