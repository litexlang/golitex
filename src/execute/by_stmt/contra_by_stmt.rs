use super::helpers_by_stmt::impossible_proof_error_message;
use crate::prelude::*;

impl Runtime {
    pub fn exec_by_contra_stmt(&mut self, stmt: &ByContraStmt) -> Result<StmtResult, RuntimeError> {
        let to_prove_fact: Fact = stmt.to_prove.clone().into();
        self.verify_fact_well_defined(&to_prove_fact, &VerifyState::new(0, false))
            .map_err(|verify_error| {
                RuntimeError::ExecStmtError({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message = format!("by contra: failed to prove `{}`", to_prove_fact);
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

        let (exec_proof_inside_results, last_error) = self.run_in_local_env(|rt| {
            let mut inside_results: Vec<StmtResult> = Vec::new();

            let reverse_to_prove_fact = stmt.to_prove.make_reversed();
            rt.store_atomic_fact_without_well_defined_verified_and_infer(reverse_to_prove_fact)
                .map_err(|store_fact_error| {
                    RuntimeError::ExecStmtError({
                        let __stmt: Stmt = stmt.clone().into();
                        let __message =
                            format!("by contra: failed to know reverse of `{}`", to_prove_fact);
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

            let mut last_error: Option<RuntimeError> = None;
            for proof_stmt in stmt.proof.iter() {
                let exec_stmt_result = rt.exec_stmt(proof_stmt);
                match exec_stmt_result {
                    Ok(result) => inside_results.push(result),
                    Err(statement_error) => {
                        last_error = Some(statement_error);
                        break;
                    }
                }
            }

            let verify_impossible_fact_result =
                rt.verify_atomic_fact(&stmt.impossible_fact, &VerifyState::new(0, false))?;
            if verify_impossible_fact_result.is_unknown() {
                return Err(RuntimeError::ExecStmtError({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message = impossible_proof_error_message(&stmt.impossible_fact, None);
                    let __cause = None;
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

            let verify_reversed_impossible_fact_result = rt.verify_atomic_fact(
                &stmt.impossible_fact.make_reversed(),
                &VerifyState::new(0, false),
            )?;
            if verify_reversed_impossible_fact_result.is_unknown() {
                return Err(RuntimeError::ExecStmtError({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message = impossible_proof_error_message(&stmt.impossible_fact, None);
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

            Ok((inside_results, last_error))
        })?;

        if let Some(last_error) = last_error {
            return Err(RuntimeError::ExecStmtError({
                let __stmt: Stmt = stmt.clone().into();
                let __message = "by contra: failed to execute proof".to_string();
                let __cause = Some(last_error);
                let __inside = exec_proof_inside_results;
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

        let to_prove_fact_display_string = to_prove_fact.to_string();
        let infer_result = self
            .store_fact_without_well_defined_verified_and_infer(to_prove_fact)
            .map_err(|store_fact_error| {
                RuntimeError::ExecStmtError({
                    let __stmt: Stmt = stmt.clone().into();
                    let __message = format!(
                        "by contra: failed to release `{}`",
                        to_prove_fact_display_string
                    );
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

        Ok((NonFactualStmtSuccess::new(
            stmt.clone().into(),
            infer_result,
            exec_proof_inside_results,
        ))
        .into())
    }
}
