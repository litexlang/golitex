use crate::prelude::*;

impl Runtime {
    pub fn exec_try_stmt(&mut self, stmt: &TryStmt) -> Result<StmtResult, RuntimeError> {
        let committed_results =
            self.run_in_local_env_and_commit(|rt| rt.exec_try_proof_steps(stmt))?;

        Ok(
            SuccessProofBlockStmtResult::TryStmt(Box::new(SuccessTryStmtResult {
                statement: stmt.clone(),
                common: SuccessStmtCommonResult::new(SuccessInferResult::new()),
                proof: Some(SuccessTryProofResult {
                    proof_steps: committed_results,
                }),
            }))
            .into(),
        )
    }

    fn exec_try_proof_steps(&mut self, stmt: &TryStmt) -> Result<Vec<StmtResult>, RuntimeError> {
        let mut results = Vec::new();
        let proof_len = stmt.proof.len();
        for (proof_index, proof_stmt) in stmt.proof.iter().enumerate() {
            match self.execute_statement(proof_stmt) {
                Ok(result) => {
                    if result.is_unknown() {
                        return Err(UnknownRuntimeError(RuntimeErrorStruct::new_with_output(
                            Some(proof_stmt.clone()),
                            "try failed: proof step is unknown".to_string(),
                            proof_stmt.line_file(),
                            None,
                            vec![],
                            RuntimeErrorOutput::proof_step_unknown(
                                proof_stmt.clone(),
                                proof_index + 1,
                                proof_len,
                                &result,
                            ),
                        ))
                        .into());
                    }
                    results.push(result);
                }
                Err(statement_error) => {
                    return Err(short_exec_error(
                        stmt.clone().into(),
                        proof_stmt.to_string(),
                        Some(statement_error),
                        vec![],
                    ));
                }
            }
        }
        Ok(results)
    }
}
