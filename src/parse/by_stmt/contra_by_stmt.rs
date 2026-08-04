use crate::prelude::*;

impl Runtime {
    /// `by contra:` then a `?` goal block, optional proof statements, then `impossible` atomic fact.
    pub fn parse_by_contra_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CONTRA)?;
        if tb.current()? != COLON {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by contra no longer accepts a goal on the header; use `by contra:` followed by `? <fact>`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() || tb.body.len() < 2 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by contra: expects a `? <fact>` goal block and impossible ... tail"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let to_prove = self.parse_goal_fact_block(&mut tb.body[0], "by contra")?;

        let n = tb.body.len();
        let proof_hi = n.saturating_sub(1);
        let (proof, impossible_fact) =
            self.run_in_local_proof_parsing_scope(|this| -> Result<_, RuntimeError> {
                let mut proof = Vec::new();
                if 1 < proof_hi {
                    for block in tb.body[1..proof_hi].iter_mut() {
                        proof.push(this.parse_stmt(block)?);
                    }
                }
                let last_block = tb.body.last_mut().ok_or_else(|| {
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "Expected body".to_string(),
                            tb.line_file.clone(),
                        ),
                    ))
                })?;
                last_block.skip_token(IMPOSSIBLE)?;
                let impossible_fact = this.parse_atomic_fact(last_block, true)?;
                Ok((proof, impossible_fact))
            })?;
        Ok(ByContraStmt::new(to_prove, proof, impossible_fact, tb.line_file.clone()).into())
    }
}
