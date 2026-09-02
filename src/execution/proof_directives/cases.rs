use super::support::impossible_proof_error_message;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_cases_stmt(&mut self, stmt: &ByCasesStmt) -> Result<StmtResult, RuntimeError> {
        let goal_well_definedness = self.exec_by_cases_stmt_verify_well_definedness(stmt)?;
        let result = self.exec_by_cases_stmt_verify_process(stmt, goal_well_definedness)?;
        let infer_result = self.exec_by_cases_stmt_affect_environment(stmt)?;

        Ok(result.with_infers(infer_result))
    }

    /// Mathematical contract: every requested conclusion of a case proof must
    /// be a meaningful fact; the accepted quantified-goal shape must also be
    /// representable by the case engine before branch coverage is attempted.
    fn exec_by_cases_stmt_verify_well_definedness(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<Vec<WellDefinedFactResult>, RuntimeError> {
        let mut goal_well_definedness = Vec::with_capacity(stmt.then_facts.len());
        for fact in stmt.then_facts.iter() {
            goal_well_definedness.push(
                self.verify_fact_well_defined_result(fact, &VerifyState::initial())
                    .map_err(|verify_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            format!("by cases: failed to prove `{}`", fact),
                            Some(verify_error),
                            vec![],
                        )
                    })?,
            );
        }

        if stmt
            .then_facts
            .iter()
            .any(|f| matches!(f, Fact::ForallFactWithIff(_)))
        {
            return Err(short_exec_error(
                stmt.clone().into(),
                "by cases: `?` with `forall`/`iff` (forall-iff) is not supported; use a plain `forall` goal"
                    .to_string(),
                None,
                vec![],
            ));
        }
        if stmt
            .then_facts
            .iter()
            .filter(|f| matches!(f, Fact::ForallFact(_)))
            .count()
            > 1
        {
            return Err(short_exec_error(
                stmt.clone().into(),
                "by cases: `?` goals may contain at most one `forall` fact".to_string(),
                None,
                vec![],
            ));
        }
        if stmt
            .then_facts
            .get(0)
            .is_some_and(|f| !matches!(f, Fact::ForallFact(_)))
            && stmt
                .then_facts
                .iter()
                .any(|f| matches!(f, Fact::ForallFact(_)))
        {
            return Err(short_exec_error(
                stmt.clone().into(),
                "by cases: when `?` goals include `forall`, the `forall` must be listed first"
                    .to_string(),
                None,
                vec![],
            ));
        }
        if stmt
            .then_facts
            .iter()
            .any(|f| matches!(f, Fact::ForallFact(_)))
            && stmt.impossible_facts.iter().any(|o| o.is_some())
        {
            return Err(short_exec_error(
                stmt.clone().into(),
                "by cases: `?` with `forall` cannot be used in the same statement as a case arm that ends with `impossible`"
                    .to_string(),
                None,
                vec![],
            ));
        }

        Ok(goal_well_definedness)
    }

    fn exec_by_cases_stmt_verify_process(
        &mut self,
        stmt: &ByCasesStmt,
        goal_well_definedness: Vec<WellDefinedFactResult>,
    ) -> Result<StmtResult, RuntimeError> {
        let coverage_check = self.exec_by_cases_stmt_verify_cases_cover_all_situations(stmt)?;
        let mut branches = Vec::with_capacity(stmt.cases.len());

        for case_index in 0..stmt.cases.len() {
            branches.push(
                self.run_in_local_env(|rt| rt.exec_by_cases_stmt_for_one_case(stmt, case_index))?,
            );
        }

        let by_verification = SuccessVerifyByCasesResult::new(
            goal_well_definedness,
            coverage_check,
            stmt.then_facts.clone(),
            branches,
        );

        Ok(
            SuccessByStmtResult::ByCasesStmt(Box::new(SuccessByCasesStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                verification: Some(by_verification),
            }))
            .into(),
        )
    }

    pub fn exec_by_cases_stmt_affect_environment(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<SuccessInferResult, RuntimeError> {
        let mut infer_result = SuccessInferResult::new();
        for then_fact in stmt.then_facts.iter() {
            let one_then_fact_infer_result = if self.current_execution_is_trusted_file() {
                self.store_fact_with_trust_and_infer_with_reason(
                    then_fact.clone(),
                    InferReason::StatementWithVerification,
                )
            } else {
                self.store_with_well_defined_verification_and_infer_with_default_verify_state(
                    then_fact.clone(),
                )
            }
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by cases: failed to release `{}`", then_fact),
                    Some(store_fact_error),
                    vec![],
                )
            })?;
            infer_result.new_infer_result_inside(one_then_fact_infer_result);
        }
        Ok(infer_result)
    }

    pub fn exec_by_cases_stmt_affect_environment_only(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_by_cases_stmt_affect_environment(stmt)?;
        Ok(
            SuccessByStmtResult::ByCasesStmt(Box::new(SuccessByCasesStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(infer_result),
                verification: None,
            }))
            .into(),
        )
    }

    fn exec_by_cases_stmt_verify_cases_cover_all_situations(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<VerifyFactResult, RuntimeError> {
        let all_cases_or_fact: Fact =
            OrFact::new(stmt.cases.clone(), stmt.line_file.clone()).into();
        let vs = VerifyState::initial();
        let result = if let Some(Fact::ForallFact(ff)) = stmt.then_facts.first() {
            self.run_in_local_env(|rt| {
                rt.forall_assume_params_and_dom_in_current_env(ff, &vs)?;
                rt.verify_fact_or_error(&all_cases_or_fact, &vs)
            })
            .map_err(|verify_error| {
                short_exec_error(
                    stmt.clone().into(),
                    "by cases: cannot verify that all cases cover all situations".to_string(),
                    Some(verify_error),
                    vec![],
                )
            })?
        } else {
            self.verify_fact_or_error(&all_cases_or_fact, &vs)
                .map_err(|verify_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        "by cases: cannot verify that all cases cover all situations".to_string(),
                        Some(verify_error),
                        vec![],
                    )
                })?
        };
        Ok(result)
    }

    fn exec_by_cases_stmt_prove_then_facts_under_case(
        &mut self,
        stmt: &ByCasesStmt,
        case_index: usize,
        proof_steps: &mut Vec<StmtResult>,
    ) -> Result<Vec<VerifyFactResult>, RuntimeError> {
        let mut conclusion_checks = Vec::with_capacity(stmt.then_facts.len());
        for then_fact in stmt.then_facts.iter() {
            let exec_fact_result =
                self.verify_fact_or_error(then_fact, &VerifyState::initial())
                    .map_err(|statement_error| {
                        let mut diagnostics = std::mem::take(proof_steps);
                        short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "by cases: failed to prove `{}` under case `{}`",
                                then_fact, stmt.cases[case_index]
                            ),
                            Some(statement_error),
                            diagnostics,
                        )
                    })?;
            self.store_without_well_defined_verification_and_infer(then_fact.clone())?;
            conclusion_checks.push(exec_fact_result);
        }
        Ok(conclusion_checks)
    }

    fn exec_by_cases_stmt_for_one_case(
        &mut self,
        stmt: &ByCasesStmt,
        case_index: usize,
    ) -> Result<SuccessVerifyByCaseBranchResult, RuntimeError> {
        let case_fact = &stmt.cases[case_index];
        let case_fact_as_fact: Fact = case_fact.clone().into();
        let case_label = case_fact.to_string();
        let mut proof_steps: Vec<StmtResult> = Vec::new();
        let vs = VerifyState::initial();

        if let Some(Fact::ForallFact(ff)) = stmt.then_facts.first() {
            let assumption_infer_result = self
                .forall_assume_params_and_dom_in_current_env(ff, &vs)
                .map_err(|e| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by cases: failed to open `forall` parameters and dom for goal `{}`",
                            ff
                        ),
                        Some(e),
                        vec![],
                    )
                })?;
            let mut infer_acc = SuccessInferResult::new();

            let mut case_assumption_infers = self
                .store_and_chain_atomic_fact_without_well_defined_verified_and_infer(
                    case_fact.clone(),
                )
                .map_err(|store_fact_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!("by cases: failed to assume case `{}`", case_fact),
                        Some(store_fact_error),
                        vec![],
                    )
                })?;
            self.attach_known_fact_ids_to_infer_result(&mut case_assumption_infers)?;
            let case_fact_id = self
                .known_fact_id_for_fact(&case_fact_as_fact)?
                .ok_or_else(|| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!("by cases: case assumption `{}` has no FactId", case_fact),
                        None,
                        vec![],
                    )
                })?;
            let assumption_components = case_assumption_components_with_fact_ids(self, case_fact)?;

            for proof_stmt in stmt.proofs[case_index].iter() {
                let exec_stmt_result = self.execute_statement(proof_stmt);
                match exec_stmt_result {
                    Ok(result) => proof_steps.push(result),
                    Err(statement_error) => {
                        return Err(short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "by cases: failed while executing proof under case `{}`",
                                case_fact
                            ),
                            Some(statement_error),
                            proof_steps,
                        ));
                    }
                }
            }

            let forall_then_result = self.forall_verify_then_facts_in_current_env(
                ff,
                &vs,
                &mut infer_acc,
                assumption_infer_result,
                Some(&case_label),
            )?;
            if !forall_then_result.is_success() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by cases: failed to prove `forall` goal under case `{}`",
                        case_fact
                    ),
                    None,
                    proof_steps,
                ));
            }
            let forall_then_result = self.complete_fact_proof_result(
                &Fact::ForallFact(ff.clone()),
                forall_then_result,
                &vs,
            )?;
            let mut conclusion_checks = vec![forall_then_result];

            for then_fact in stmt.then_facts.iter().skip(1) {
                let exec_fact_result =
                    self.verify_fact_or_error(then_fact, &VerifyState::initial())
                        .map_err(|statement_error| {
                            short_exec_error(
                                stmt.clone().into(),
                                format!(
                                    "by cases: failed to prove `{}` under case `{}`",
                                    then_fact, case_fact
                                ),
                                Some(statement_error),
                                std::mem::take(&mut proof_steps),
                            )
                        })?;
                self.store_without_well_defined_verification_and_infer(then_fact.clone())?;
                conclusion_checks.push(exec_fact_result);
            }

            return Ok(SuccessVerifyByCaseBranchResult {
                assumption: case_fact.clone(),
                assumption_fact_id: case_fact_id,
                proof_scope: SuccessVerifyLocalProofScopeResult::new(
                    case_assumption_infers,
                    assumption_components,
                ),
                proof_steps,
                exit: SuccessVerifyByCaseBranchExitResult::Conclusions(Box::new(
                    SuccessVerifyByCaseConclusionsResult {
                        checks: conclusion_checks,
                    },
                )),
            });
        }

        let mut case_assumption_infers = self
            .store_and_chain_atomic_fact_without_well_defined_verified_and_infer(case_fact.clone())
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by cases: failed to assume case `{}`", case_fact),
                    Some(store_fact_error),
                    vec![],
                )
            })?;
        self.attach_known_fact_ids_to_infer_result(&mut case_assumption_infers)?;
        let case_fact_id = self
            .known_fact_id_for_fact(&case_fact_as_fact)?
            .ok_or_else(|| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by cases: case assumption `{}` has no FactId", case_fact),
                    None,
                    vec![],
                )
            })?;
        let assumption_components = case_assumption_components_with_fact_ids(self, case_fact)?;

        for proof_stmt in stmt.proofs[case_index].iter() {
            let exec_stmt_result = self.execute_statement(proof_stmt);
            match exec_stmt_result {
                Ok(result) => proof_steps.push(result),
                Err(statement_error) => {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by cases: failed while executing proof under case `{}`",
                            case_fact
                        ),
                        Some(statement_error),
                        proof_steps,
                    ));
                }
            }
        }

        if let Some(impossible_fact) = &stmt.impossible_facts[case_index] {
            let verify_state = VerifyState::initial();
            let verify_impossible_fact_result = self
                .verify_atomic_fact(impossible_fact, &verify_state)
                .map_err(|verify_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        impossible_proof_error_message(
                            impossible_fact,
                            Some(case_fact.to_string()),
                        ),
                        Some(verify_error),
                        vec![],
                    )
                })?;

            if verify_impossible_fact_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    impossible_proof_error_message(impossible_fact, Some(case_fact.to_string())),
                    None,
                    vec![],
                ));
            }

            let negated_impossible_fact =
                impossible_fact
                    .logical_negation()
                    .map_err(|negation_error| {
                        short_exec_error(
                            stmt.clone().into(),
                            impossible_proof_error_message(
                                impossible_fact,
                                Some(case_fact.to_string()),
                            ),
                            Some(negation_error),
                            vec![],
                        )
                    })?;
            let verify_negated_impossible_fact_result = self
                .verify_atomic_fact(&negated_impossible_fact, &verify_state)
                .map_err(|verify_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        impossible_proof_error_message(
                            impossible_fact,
                            Some(case_fact.to_string()),
                        ),
                        Some(verify_error),
                        vec![],
                    )
                })?;

            if verify_negated_impossible_fact_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    impossible_proof_error_message(impossible_fact, Some(case_fact.to_string())),
                    None,
                    vec![],
                ));
            }

            return Ok(SuccessVerifyByCaseBranchResult {
                assumption: case_fact.clone(),
                assumption_fact_id: case_fact_id,
                proof_scope: SuccessVerifyLocalProofScopeResult::new(
                    case_assumption_infers,
                    assumption_components,
                ),
                proof_steps,
                exit: SuccessVerifyByCaseBranchExitResult::Contradiction(Box::new(
                    SuccessVerifyByCaseContradictionResult {
                        impossible_fact: impossible_fact.clone(),
                        contradiction: SuccessVerifyContradictionResult {
                            impossible_check: Box::new(verify_impossible_fact_result),
                            negated_impossible_check: Box::new(
                                verify_negated_impossible_fact_result,
                            ),
                        },
                    },
                )),
            });
        }

        let conclusion_checks = self.exec_by_cases_stmt_prove_then_facts_under_case(
            stmt,
            case_index,
            &mut proof_steps,
        )?;
        Ok(SuccessVerifyByCaseBranchResult {
            assumption: case_fact.clone(),
            assumption_fact_id: case_fact_id,
            proof_scope: SuccessVerifyLocalProofScopeResult::new(
                case_assumption_infers,
                assumption_components,
            ),
            proof_steps,
            exit: SuccessVerifyByCaseBranchExitResult::Conclusions(Box::new(
                SuccessVerifyByCaseConclusionsResult {
                    checks: conclusion_checks,
                },
            )),
        })
    }
}

fn case_assumption_components_with_fact_ids(
    runtime: &mut Runtime,
    case_fact: &AndChainAtomicFact,
) -> Result<Vec<(FactId, Fact)>, RuntimeError> {
    let components = match case_fact {
        AndChainAtomicFact::AtomicFact(_) => Vec::new(),
        AndChainAtomicFact::AndFact(and_fact) => and_fact
            .facts
            .iter()
            .cloned()
            .map(Fact::from)
            .collect::<Vec<_>>(),
        AndChainAtomicFact::ChainFact(chain_fact) => chain_fact
            .facts()?
            .into_iter()
            .map(Fact::from)
            .collect::<Vec<_>>(),
    };
    let mut retained = Vec::with_capacity(components.len());
    for component in components {
        // `Environment::store_and_fact` deliberately indexes each atomic
        // conjunct for verification without giving that projection a cache
        // identity.  To-Lean needs stable identities after this local
        // environment closes, so allocate/cache them while the branch is live.
        // The IR still records the real derivation as ConjunctionProjection;
        // assigning an ID here does not turn the component into a premise.
        let fact_id = runtime.store_fact_cache_keys_with_nested_obj_binders(&component)?;
        retained.push((fact_id, component));
    }
    Ok(retained)
}
