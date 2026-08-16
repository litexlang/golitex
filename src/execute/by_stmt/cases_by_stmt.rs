use super::helpers_by_stmt::impossible_proof_error_message;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_cases_stmt(&mut self, stmt: &ByCasesStmt) -> Result<StmtResult, RuntimeError> {
        self.exec_by_cases_stmt_verify_well_definedness(stmt)?;
        let result = self.exec_by_cases_stmt_verify_process(stmt)?;
        let infer_result = self.exec_by_cases_stmt_affect_environment(stmt)?;

        Ok(result.with_infers(infer_result))
    }

    /// Mathematical contract: every requested conclusion of a case proof must
    /// be a meaningful fact; the accepted quantified-goal shape must also be
    /// representable by the case engine before branch coverage is attempted.
    fn exec_by_cases_stmt_verify_well_definedness(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<(), RuntimeError> {
        for fact in stmt.then_facts.iter() {
            self.verify_fact_well_defined(fact, &UseContextVerifyState::new(0, false))
                .map_err(|verify_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!("by cases: failed to prove `{}`", fact),
                        Some(verify_error),
                        vec![],
                    )
                })?;
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

        Ok(())
    }

    fn exec_by_cases_stmt_verify_process(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let mut inside_results =
            vec![self.exec_by_cases_stmt_verify_cases_cover_all_situations(stmt)?];
        let mut case_result_counts = Vec::new();
        let mut case_fact_ids = Vec::new();
        let mut proof_scopes = Vec::new();

        for case_index in 0..stmt.cases.len() {
            let (case_fact_id, mut case_results, proof_scope) = self.run_in_local_env(|rt| {
                let captures_well_definedness = rt.captures_litex_to_lean_well_definedness();
                if captures_well_definedness {
                    rt.begin_statement_well_definedness_capture();
                }
                let branch_result = rt.exec_by_cases_stmt_for_one_case(stmt, case_index);
                match branch_result {
                    Ok((
                        case_fact_id,
                        case_assumption_infers,
                        assumption_components,
                        case_results,
                    )) => {
                        let well_definedness = if captures_well_definedness {
                            rt.end_statement_well_definedness_capture()?
                        } else {
                            WellDefinednessCertificate::default()
                        };
                        Ok((
                            case_fact_id,
                            case_results,
                            LocalProofScopeVerificationResult::new(
                                case_assumption_infers,
                                assumption_components,
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
            case_fact_ids.push(case_fact_id);
            case_result_counts.push(case_results.len());
            proof_scopes.push(proof_scope);
            inside_results.append(&mut case_results);
        }

        let proof_step_counts = stmt
            .proofs
            .iter()
            .map(|proof| proof.len())
            .collect::<Vec<_>>();
        let by_verification = ByCasesVerificationResult::new(
            stmt.cases.clone(),
            case_fact_ids,
            stmt.then_facts.clone(),
            proof_step_counts,
            case_result_counts,
            proof_scopes,
            stmt.impossible_facts.clone(),
        )
        .into();

        Ok(NonFactualStmtSuccess::new_with_by_verification(
            stmt.clone().into(),
            InferResult::new(),
            inside_results,
            by_verification,
        )
        .into())
    }

    pub(crate) fn exec_by_cases_stmt_affect_environment(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<InferResult, RuntimeError> {
        let mut infer_result = InferResult::new();
        for then_fact in stmt.then_facts.iter() {
            let one_then_fact_infer_result = if self.current_execution_is_trusted_file() {
                self.store_trusted_fact_and_infer_with_reason(
                    then_fact.clone(),
                    InferReason::VerifiedStatement,
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

    pub(crate) fn exec_by_cases_stmt_affect_environment_only(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let infer_result = self.exec_by_cases_stmt_affect_environment(stmt)?;
        Ok(NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, vec![]).into())
    }

    fn exec_by_cases_stmt_verify_cases_cover_all_situations(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<StmtResult, RuntimeError> {
        let all_cases_or_fact: Fact =
            OrFact::new(stmt.cases.clone(), stmt.line_file.clone()).into();
        let vs = UseContextVerifyState::new(0, false);
        let result = if let Some(Fact::ForallFact(ff)) = stmt.then_facts.first() {
            self.run_in_local_env(|rt| {
                rt.forall_assume_params_and_dom_in_current_env(ff, &vs)?;
                rt.verify_fact_return_err_if_not_true(&all_cases_or_fact, &vs)
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
            self.verify_fact_return_err_if_not_true(&all_cases_or_fact, &vs)
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
        inside_results: &mut Vec<StmtResult>,
    ) -> Result<(), RuntimeError> {
        for then_fact in stmt.then_facts.iter() {
            let exec_fact_result = self.exec_fact(then_fact).map_err(|statement_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by cases: failed to prove `{}` under case `{}`",
                        then_fact, stmt.cases[case_index]
                    ),
                    Some(statement_error),
                    std::mem::take(inside_results),
                )
            })?;
            inside_results.push(exec_fact_result);
        }
        Ok(())
    }

    fn exec_by_cases_stmt_for_one_case(
        &mut self,
        stmt: &ByCasesStmt,
        case_index: usize,
    ) -> Result<(FactId, InferResult, Vec<(FactId, Fact)>, Vec<StmtResult>), RuntimeError> {
        let case_fact = &stmt.cases[case_index];
        let case_fact_as_fact: Fact = case_fact.clone().into();
        let case_label = case_fact.to_string();
        let mut inside_results: Vec<StmtResult> = Vec::new();
        let vs = UseContextVerifyState::new(0, false);

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
            let mut infer_acc = InferResult::new();

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
                let exec_stmt_result = self.exec_stmt(proof_stmt);
                match exec_stmt_result {
                    Ok(result) => inside_results.push(result),
                    Err(statement_error) => {
                        return Err(short_exec_error(
                            stmt.clone().into(),
                            format!(
                                "by cases: failed while executing proof under case `{}`",
                                case_fact
                            ),
                            Some(statement_error),
                            inside_results,
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
            if !forall_then_result.is_true() {
                inside_results.push(forall_then_result);
                return Err(short_exec_error(
                    stmt.clone().into(),
                    format!(
                        "by cases: failed to prove `forall` goal under case `{}`",
                        case_fact
                    ),
                    None,
                    inside_results,
                ));
            }
            inside_results.push(forall_then_result);

            for then_fact in stmt.then_facts.iter().skip(1) {
                let exec_fact_result = self.exec_fact(then_fact).map_err(|statement_error| {
                    short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by cases: failed to prove `{}` under case `{}`",
                            then_fact, case_fact
                        ),
                        Some(statement_error),
                        std::mem::take(&mut inside_results),
                    )
                })?;
                inside_results.push(exec_fact_result);
            }

            return Ok((
                case_fact_id,
                case_assumption_infers,
                assumption_components,
                inside_results,
            ));
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
            let exec_stmt_result = self.exec_stmt(proof_stmt);
            match exec_stmt_result {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        format!(
                            "by cases: failed while executing proof under case `{}`",
                            case_fact
                        ),
                        Some(statement_error),
                        inside_results,
                    ));
                }
            }
        }

        if let Some(impossible_fact) = &stmt.impossible_facts[case_index] {
            let verify_state = UseContextVerifyState::new(0, false);
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

            inside_results.push(
                (NonFactualStmtSuccess::new(
                    stmt.clone().into(),
                    InferResult::new(),
                    vec![
                        verify_impossible_fact_result,
                        verify_negated_impossible_fact_result,
                    ],
                ))
                .into(),
            );

            return Ok((
                case_fact_id,
                case_assumption_infers,
                assumption_components,
                inside_results,
            ));
        }

        self.exec_by_cases_stmt_prove_then_facts_under_case(stmt, case_index, &mut inside_results)?;
        Ok((
            case_fact_id,
            case_assumption_infers,
            assumption_components,
            inside_results,
        ))
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
