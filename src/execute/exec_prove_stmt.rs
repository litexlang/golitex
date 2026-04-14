use crate::prelude::*;

impl Runtime {
    pub fn exec_prove_stmt(&mut self, stmt: &ProveStmt) -> Result<StmtResult, RuntimeError> {
        let inside_results = self.run_in_local_env(|rt| {
            let mut inside_results: Vec<StmtResult> = Vec::new();
            for proof_stmt in &stmt.proof {
                let exec_stmt_result = rt.exec_stmt(proof_stmt);
                match exec_stmt_result {
                    Ok(result) => inside_results.push(result),
                    Err(statement_error) => {
                        return Err(RuntimeError::ExecStmtError({
                            let __stmt: Stmt = stmt.clone().into();
                            let __message = proof_stmt.to_string();
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
            Ok(inside_results)
        });

        match inside_results {
            Ok(_) => {
                Ok(
                    (NonFactualStmtSuccess::new(stmt.clone().into(), InferResult::new(), vec![]))
                        .into(),
                )
            }
            Err(inside_results_error) => Err(inside_results_error),
        }
    }
}
