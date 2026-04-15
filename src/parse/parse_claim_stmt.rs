use crate::prelude::*;

impl Runtime {
    pub fn parse_claim_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CLAIM)?;
        Ok(self.parse_multiline_fact_claim(tb)?.into())
    }

    fn parse_multiline_fact_claim(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<ClaimStmt, RuntimeError> {
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "claim : expects at least one body block (=>: fact)".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }
        let fact = {
            let first = tb.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "claim : expects at least one body block (=>: fact)".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;

            first.skip_token(PROVE)?;
            first.skip_token(COLON)?;

            let body_block = first.body.get_mut(0).ok_or_else(|| {
                RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                    None,
                    "claim =>: expects exactly one body block (the fact)".to_string(),
                    first.line_file.clone(),
                    None,
                    vec![],
                )))
            })?;
            let f = self.parse_fact(body_block)?;
            if matches!(&f, Fact::ForallFactWithIff(_)) {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "claim multiline fact cannot be iff".to_string(),
                        first.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            Ok::<Fact, RuntimeError>(f)
        }?;

        let proof: Vec<Stmt> = self.run_in_local_parsing_time_name_scope(|this| {
            tb.body
                .iter_mut()
                .skip(1)
                .map(|b| this.parse_stmt(b))
                .collect::<Result<_, _>>()
        })?;
        Ok(ClaimStmt::new(fact, proof, tb.line_file.clone()))
    }
}
