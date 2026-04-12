use crate::prelude::*;

impl Runtime {
    pub fn parse_by_extension_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token_and_colon_and_exceed_end_of_head(EXTENSION)?;

        if tb.body.is_empty() {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "by extension: expects at least one body block".to_string(),
                tb.line_file.clone(),
                None,
            ));
        }

        tb.body[0].skip_token_and_colon_and_exceed_end_of_head(PROVE)?;

        if tb.body[0].body.len() != 1 {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "by extension: prove: expects exactly one atomic fact block".to_string(),
                tb.body[0].line_file.clone(),
                None,
            ));
        }

        let to_prove_equal_fact = self.parse_atomic_fact(
            tb.body[0].body.get_mut(0).ok_or_else(|| {
                RuntimeError::new_parse_error_with_msg_position_previous_error("Expected body".to_string(), tb.line_file.clone(), None)
            })?,
            true,
        )?;

        let (left, right) = match to_prove_equal_fact {
            AtomicFact::EqualFact(equal_fact) => (equal_fact.left, equal_fact.right),
            _ => {
                return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "by extension: prove: expects equal fact".to_string(),
                    tb.line_file.clone(),
                    None,
                ));
            }
        };

        let mut proof: Vec<Stmt> = vec![];
        for block in tb.body[1..].iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }

        Ok(ByExtensionStmt::new(left, right, proof, tb.line_file.clone()).into())
    }
}
