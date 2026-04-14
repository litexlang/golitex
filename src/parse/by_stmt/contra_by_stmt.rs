use crate::prelude::*;

impl Runtime {
    /// `by contra:` then `prove:` block with exactly one atomic fact, optional proof statements, then `impossible` atomic fact.
    pub fn parse_by_contra_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CONTRA)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by contra: expected end of head after by contra:".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        if tb.body.len() < 2 {
            return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by contra: expects prove: block and impossible ... tail".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        let to_prove = {
            let prove_block = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "Expected body".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            prove_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
            if prove_block.body.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "by contra: prove: expects exactly one atomic fact block".to_string(),
                    prove_block.line_file.clone(),
                    None,
                    vec![],
                ))));
            }
            let atomic_fact_block = prove_block.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "Expected body".to_string(),
                prove_block.line_file.clone(),
                None,
                vec![],
            )))
            })?;
            self.parse_atomic_fact(atomic_fact_block, true)?
        };
        let n = tb.body.len();
        let proof_stmt_block_count = n.saturating_sub(2);
        let mut proof = Vec::with_capacity(proof_stmt_block_count);
        for block in tb.body[1..n - 1].iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }
        let mut last_block = tb.body.last_mut().ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
 None,
                "Expected body".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            )))
        })?;
        last_block.skip_token(IMPOSSIBLE)?;
        let impossible_fact = self.parse_atomic_fact(&mut last_block, true)?;
        Ok(ByContraStmt::new(to_prove, proof, impossible_fact, tb.line_file.clone()).into())
    }
}
