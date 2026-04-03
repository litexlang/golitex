use crate::prelude::*;

impl Runtime {
    pub fn parse_claim_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CLAIM)?;
        Ok(Stmt::ClaimStmt(self.parse_multiline_fact_claim(tb)?))
    }

    fn parse_multiline_fact_claim(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ClaimStmt, RuntimeError> {
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "claim : expects at least one body block (=>: fact)".to_string(),
                tb.line_file.clone(),
                None,
            ));
        }
        let fact = {
            let first = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "claim : expects at least one body block (=>: fact)".to_string(),
                    tb.line_file.clone(),
                    None,
                )
            })?;

            first.skip_token(PROVE)?;
            first.skip_token(COLON)?;

            let body_block = first.body.get_mut(0).ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "claim =>: expects exactly one body block (the fact)".to_string(),
                    first.line_file.clone(),
                    None,
                )
            })?;
            let f = self.parse_fact(body_block)?;
            if matches!(&f, Fact::ForallFactWithIff(_)) {
                return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "claim multiline fact cannot be iff".to_string(),
                    first.line_file.clone(),
                    None,
                ));
            }
            Ok::<Fact, RuntimeError>(f)
        }?;

        let proof: Vec<Stmt> = tb
            .body
            .iter_mut()
            .skip(1)
            .map(|b| self.parse_stmt(b))
            .collect::<Result<_, _>>()?;
        Ok(ClaimStmt::new(fact, proof, tb.line_file.clone()))
    }
}
