use crate::prelude::*;

impl Runtime {
    pub fn exec_sketch_stmt(&mut self, stmt: &SketchStmt) -> Result<StmtResult, RuntimeError> {
        let result = self.run_in_local_env(|rt| {
            let body_result = (|| {
                let mut inside_results: Vec<StmtResult> = Vec::new();
                for proof_stmt in &stmt.proof {
                    match rt.execute_statement(proof_stmt) {
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
                for result in inside_results.iter_mut() {
                    rt.attach_known_fact_ids_to_stmt_result(result)?;
                }
                Ok(inside_results)
            })();
            match body_result {
                Ok(inside_results) => Ok((
                    inside_results,
                    SuccessVerifyLocalProofScopeResult::new(SuccessInferResult::new(), Vec::new()),
                )),
                Err(error) => Err(error),
            }
        });

        match result {
            Ok((inside_results, proof_scope)) => Ok(SuccessProofBlockStmtResult::SketchStmt(
                Box::new(SuccessSketchStmtResult {
                    statement: stmt.clone(),
                    common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                    proof: Some(SuccessSketchProofResult {
                        proof_scope,
                        proof_steps: inside_results,
                    }),
                }),
            )
            .into()),
            Err(inside_results_error) => Err(inside_results_error),
        }
    }
}
