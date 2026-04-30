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
                        return Err(short_exec_error(
                            stmt.clone().into(),
                            proof_stmt.to_string(),
                            Some(statement_error),
                            std::mem::take(&mut inside_results),
                        ));
                    }
                }
            }
            Ok(inside_results)
        });

        match inside_results {
            Ok(inside_results) => Ok(NonFactualStmtSuccess::new(
                stmt.clone().into(),
                InferResult::new(),
                inside_results,
            )
            .into()),
            Err(inside_results_error) => Err(inside_results_error),
        }
    }
}
