use crate::prelude::*;

impl Runtime {
    pub fn parse_claim_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(CLAIM)?;
        Ok(Stmt::ClaimStmt(self.parse_multiline_fact_claim(tb)?))
    }

    fn parse_multiline_fact_claim(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ClaimStmt, ParsingError> {
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(ParsingError::new(
                "claim : expects at least one body block (=>: fact)".to_string(),
                tb.line_file,
                None,
            ));
        }
        let fact = {
            let first = tb.body.get_mut(0).ok_or_else(|| {
                ParsingError::new(
                    "claim : expects at least one body block (=>: fact)".to_string(),
                    tb.line_file,
                    None,
                )
            })?;

            first.skip_token(PROVE)?;
            first.skip_token(COLON)?;

            let body_block = first.body.get_mut(0).ok_or_else(|| {
                ParsingError::new(
                    "claim =>: expects exactly one body block (the fact)".to_string(),
                    first.line_file,
                    None,
                )
            })?;
            let f = self.parse_fact(body_block)?;
            if matches!(&f, Fact::ForallFactWithIff(_)) {
                return Err(ParsingError::new(
                    "claim multiline fact cannot be iff".to_string(),
                    first.line_file,
                    None,
                ));
            }
            Ok(f)
        }?;

        let proof: Vec<Stmt> = tb
            .body
            .iter_mut()
            .skip(1)
            .map(|b| self.parse_stmt(b))
            .collect::<Result<_, _>>()?;
        Ok(ClaimStmt::new(fact, proof, tb.line_file))
    }
}
