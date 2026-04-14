use super::helpers_by_stmt::impossible_proof_error_message;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_cases_stmt(&mut self, stmt: &ByCasesStmt) -> Result<StmtResult, RuntimeError> {
        for fact in stmt.then_facts.iter() {
            self.verify_fact_well_defined(fact, &VerifyState::new(0, false))
                .map_err(|verify_error| {
                    RuntimeError::ExecStmtError({
                        let __stmt: Stmt = stmt.clone().into();
                        let __message = format!("by cases: failed to prove `{}`", fact);
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
        }

        self.exec_by_cases_stmt_verify_cases_cover_all_situations(stmt)?;

        let mut inside_results: Vec<StmtResult> = Vec::new();
        for case_index in 0..stmt.cases.len() {
            let one_case_result =
                self.run_in_local_env(|rt| rt.exec_by_cases_stmt_for_one_case(stmt, case_index));

            match one_case_result {
                Ok(mut one_case_inside_results) => {
                    inside_results.append(&mut one_case_inside_results);
                }
                Err(exec_stmt_error) => {
                    return Err(exec_stmt_error);
                }
            }
        }

        let mut infer_result = InferResult::new();
        for then_fact in stmt.then_facts.iter() {
            let one_then_fact_infer_result = self
                .store_fact_without_well_defined_verified_and_infer(then_fact.clone())
                .map_err(|store_fact_error| {
                    RuntimeError::ExecStmtError({
                        let __stmt: Stmt = stmt.clone().into();
                        let __message = format!("by cases: failed to release `{}`", then_fact);
                        let __cause = Some(store_fact_error);
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
            infer_result.new_infer_result_inside(one_then_fact_infer_result);
        }

        Ok((NonFactualStmtSuccess::new(stmt.clone().into(), infer_result, inside_results)).into())
    }

    fn exec_by_cases_stmt_verify_cases_cover_all_situations(
        &mut self,
        stmt: &ByCasesStmt,
    ) -> Result<(), RuntimeError> {
        let all_cases_or_fact: Fact =
            OrFact::new(stmt.cases.clone(), stmt.line_file.clone()).into();
        self.verify_fact_return_err_if_not_true(&all_cases_or_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                RuntimeError::from({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message =
                        "by cases: cannot verify that all cases cover all situations".to_string();
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
        Ok(())
    }

    fn exec_by_cases_stmt_prove_then_facts_under_case(
        &mut self,
        stmt: &ByCasesStmt,
        case_index: usize,
        inside_results: &mut Vec<StmtResult>,
    ) -> Result<(), RuntimeError> {
        for then_fact in stmt.then_facts.iter() {
            let exec_fact_result = self.exec_fact(then_fact).map_err(|statement_error| {
                RuntimeError::from({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message = format!(
                        "by cases: failed to prove `{}` under case `{}`",
                        then_fact, stmt.cases[case_index]
                    );
                    let __cause = Some(statement_error);
                    let __inside = std::mem::take(inside_results);
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
        let mut inside_results: Vec<StmtResult> = Vec::new();

        self.store_and_chain_atomic_fact_without_well_defined_verified_and_infer(case_fact.clone())
            .map_err(|store_fact_error| {
                RuntimeError::from({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message = format!("by cases: failed to assume case `{}`", case_fact);
                    let __cause = Some(store_fact_error);
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

        for proof_stmt in stmt.proofs[case_index].iter() {
            let exec_stmt_result = self.exec_stmt(proof_stmt);
            match exec_stmt_result {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    return Err(RuntimeError::from({
                        let __stmt: Stmt = stmt.clone().into();
                        let __message = format!(
                            "by cases: failed while executing proof under case `{}`",
                            case_fact
                        );
                        let __cause = Some(statement_error);
                        let __inside = inside_results;
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
                    }));
                }
            }
        }

        if let Some(impossible_fact) = &stmt.impossible_facts[case_index] {
            let verify_state = VerifyState::new(0, false);
            let verify_impossible_fact_result = self
                .verify_atomic_fact(impossible_fact, &verify_state)
                .map_err(|verify_error| {
                    RuntimeError::from({
                        let __stmt: Stmt = stmt.clone().into();
                        let __message = impossible_proof_error_message(
                            impossible_fact,
                            Some(case_fact.to_string()),
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

            if verify_impossible_fact_result.is_unknown() {
                return Err(RuntimeError::from({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message = impossible_proof_error_message(
                        impossible_fact,
                        Some(case_fact.to_string()),
                    );
                    let __cause = None;
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
                }));
            }

            let verify_reversed_impossible_fact_result = self
                .verify_atomic_fact(&impossible_fact.make_reversed(), &verify_state)
                .map_err(|verify_error| {
                    RuntimeError::from({
                        let __stmt: Stmt = stmt.clone().into();
                        let __message = impossible_proof_error_message(
                            impossible_fact,
                            Some(case_fact.to_string()),
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

            if verify_reversed_impossible_fact_result.is_unknown() {
                return Err(RuntimeError::from({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message = impossible_proof_error_message(
                        impossible_fact,
                        Some(case_fact.to_string()),
                    );
                    let __cause = None;
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
                }));
            }

            inside_results.push(
                (NonFactualStmtSuccess::new(
                    stmt.clone().into(),
                    InferResult::new(),
                    vec![
                        verify_impossible_fact_result,
                        verify_reversed_impossible_fact_result,
                    ],
                ))
                .into(),
            );

            return Ok(inside_results);
        }

        self.exec_by_cases_stmt_prove_then_facts_under_case(stmt, case_index, &mut inside_results)?;
        Ok(inside_results)
    }
}
