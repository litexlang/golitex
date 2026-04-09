use crate::prelude::*;

impl Runtime {
    pub fn exec_prove_stmt(
        &mut self,
        stmt: &ProveStmt,
    ) -> Result<StmtExecResult, RuntimeError> {
        let inside_results = self.run_in_local_env(|rt| rt.exec_prove_stmt_body(stmt));

        match inside_results {
            Ok(_) => Ok(StmtExecResult::NonFactualStmtSuccess(
                NonFactualStmtSuccess::new(
                    Stmt::ProveStmt(stmt.clone()),
                    InferResult::new(),
                    vec![],
                ),
            )),
            Err(inside_results_error) => Err(RuntimeError::from(inside_results_error)),
        }
    }

    fn exec_prove_stmt_body(
        &mut self,
        stmt: &ProveStmt,
    ) -> Result<Vec<StmtExecResult>, RuntimeError> {
        let mut inside_results: Vec<StmtExecResult> = Vec::new();
        for proof_stmt in &stmt.proof {
            let exec_stmt_result = self.exec_stmt(proof_stmt);
            match exec_stmt_result {
                Ok(result) => inside_results.push(result),
                Err(statement_error) => {
                    return Err(RuntimeError::from(
                        RuntimeErrorStruct::exec_stmt_with_message_and_cause(
                            Stmt::ProveStmt(stmt.clone()),
                            proof_stmt.to_string(),
                            Some(statement_error),
                            inside_results,
                        ),
                    ));
                }
            }
        }
        Ok(inside_results)
    }
}
