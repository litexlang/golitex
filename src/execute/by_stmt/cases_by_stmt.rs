use super::helpers_by_stmt::impossible_proof_error_message;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_cases_stmt(&mut self, stmt: &ByCasesStmt) -> Result<StmtResult, RuntimeError> {
        for fact in stmt.then_facts.iter() {
            self.verify_fact_well_defined(fact, &VerifyState::new(0, false))
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
                "by cases: `prove:` with `forall`/`iff` (forall-iff) is not supported; use a plain `forall` goal"
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
                "by cases: `prove:` may contain at most one `forall` fact".to_string(),
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
                "by cases: when `prove:` includes `forall`, the `forall` must be listed first"
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
                "by cases: `prove:` with `forall` cannot be used in the same statement as a case arm that ends with `impossible`"
                    .to_string(),
                None,
                vec![],
            ));
        }

        let coverage = self.exec_by_cases_stmt_verify_cases_cover_all_situations(stmt)?;

        let mut accepted_cases = Vec::new();
        for case_index in 0..stmt.cases.len() {
            let inside_results =
                self.run_in_local_env(|rt| rt.exec_by_cases_stmt_for_one_case(stmt, case_index))?;
            accepted_cases.push(CaseSplitAcceptedBy::new(
                stmt.cases[case_index].clone(),
                stmt.impossible_facts[case_index].clone(),
                inside_results,
            ));
        }

        let mut infer_result = InferResult::new();
        for then_fact in stmt.then_facts.iter() {
            let one_then_fact_infer_result = self
                .verify_well_defined_and_store_and_infer_with_default_verify_state(
                    then_fact.clone(),
                )
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

        Ok((NonFactualStmtSuccess::new_with_accepted_by(
            stmt.clone().into(),
            infer_result,
            vec![],
            AcceptedByResult::case_split_with_coverage(
                stmt.then_facts.clone(),
                Some(coverage),
                accepted_cases,
            ),
        ))
        .into())
    }

    fn exec_by_cases_stmt_verify_cases_cover_all_situations(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<CaseSplitCoverage, RuntimeError> {
        let all_cases_or_fact: Fact =
            OrFact::new(stmt.cases.clone(), stmt.line_file.clone()).into();
        let vs = VerifyState::new(0, false);
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
        Ok(CaseSplitCoverage::new(all_cases_or_fact, result))
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
    ) -> Result<Vec<StmtResult>, RuntimeError> {
        let case_fact = &stmt.cases[case_index];
        let case_label = case_fact.to_string();
        let mut inside_results: Vec<StmtResult> = Vec::new();
        let vs = VerifyState::new(0, false);

        if let Some(Fact::ForallFact(ff)) = stmt.then_facts.first() {
            let mut infer_acc = self
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

            self.store_and_chain_atomic_fact_without_well_defined_verified_and_infer(
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

            return Ok(inside_results);
        }

        self.store_and_chain_atomic_fact_without_well_defined_verified_and_infer(case_fact.clone())
            .map_err(|store_fact_error| {
                short_exec_error(
                    stmt.clone().into(),
                    format!("by cases: failed to assume case `{}`", case_fact),
                    Some(store_fact_error),
                    vec![],
                )
            })?;

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
            let verify_state = VerifyState::new(0, false);
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

            let verify_reversed_impossible_fact_result = self
                .verify_atomic_fact(&impossible_fact.make_reversed(), &verify_state)
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

            if verify_reversed_impossible_fact_result.is_unknown() {
                return Err(short_exec_error(
                    stmt.clone().into(),
                    impossible_proof_error_message(impossible_fact, Some(case_fact.to_string())),
                    None,
                    vec![],
                ));
            }

            inside_results.push(
                (NonFactualStmtSuccess::new_with_accepted_by(
                    stmt.clone().into(),
                    InferResult::new(),
                    vec![
                        verify_impossible_fact_result,
                        verify_reversed_impossible_fact_result,
                    ],
                    AcceptedByResult::proof_block(None, 2),
                ))
                .into(),
            );

            return Ok(inside_results);
        }

        self.exec_by_cases_stmt_prove_then_facts_under_case(stmt, case_index, &mut inside_results)?;
        Ok(inside_results)
    }
}
