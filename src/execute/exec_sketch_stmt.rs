use crate::prelude::*;

impl Runtime {
    pub fn exec_sketch_stmt(&mut self, stmt: &SketchStmt) -> Result<StmtResult, RuntimeError> {
        let result = self.run_in_local_env(|rt| {
            let captures_well_definedness = rt.captures_well_definedness();
            if captures_well_definedness {
                rt.begin_statement_well_definedness_capture();
            }
            let body_result = (|| {
                let mut inside_results: Vec<StmtResult> = Vec::new();
                for proof_stmt in &stmt.proof {
                    match rt.exec_stmt(proof_stmt) {
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
                Ok(inside_results) => {
                    let well_definedness = if captures_well_definedness {
                        rt.end_statement_well_definedness_capture()?
                    } else {
                        WellDefinednessCertificate::default()
                    };
                    Ok((
                        inside_results,
                        LocalProofScopeVerificationResult::new(
                            InferResult::new(),
                            Vec::new(),
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
        });

        match result {
            Ok((inside_results, proof_scope)) => Ok(NonFactualStmtSuccess::new(
                stmt.clone().into(),
                InferResult::new(),
                inside_results,
            )
            .with_local_proof_scope_verification(proof_scope)
            .into()),
            Err(inside_results_error) => Err(inside_results_error),
        }
    }
}
