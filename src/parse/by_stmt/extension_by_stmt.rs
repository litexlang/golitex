use crate::prelude::*;

impl Runtime {
    /// `by extension A = B`, or `by extension:` then a `?` equality goal and proof blocks.
    pub fn parse_by_extension_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(EXTENSION)?;
        let (to_prove_equal_fact, proof) = if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            if !tb.exceed_end_of_head() || tb.body.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by extension expects a `? <equality>` goal block".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }

            let fact = self.parse_goal_atomic_fact_block(&mut tb.body[0], "by extension")?;
            let mut proof = Vec::new();
            for block in tb.body[1..].iter_mut() {
                proof.push(self.parse_stmt(block)?);
            }
            (fact, proof)
        } else {
            if !tb.body.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "inline by extension does not accept an indented body; use `by extension:` followed by `? <equality>` and proof statements"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let fact = self.parse_atomic_fact(tb, true)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "inline by extension expects exactly one equality".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            (fact, Vec::new())
        };
        let (left, right) = match to_prove_equal_fact {
            AtomicFact::EqualFact(equal_fact) => (equal_fact.left, equal_fact.right),
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by extension: goal expects equal fact".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        };

        Ok(ByExtensionStmt::new(left, right, proof, tb.line_file.clone()).into())
    }
}
