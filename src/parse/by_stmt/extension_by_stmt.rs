use crate::prelude::*;

impl Runtime {
    /// `by extension:` then a `?` goal with exactly one equality, plus proof blocks.
    pub fn parse_by_extension_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(EXTENSION)?;
        if tb.current()? != COLON {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by extension no longer accepts a goal on the header; use `by extension:` followed by `? <equality>`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() || tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by extension expects a `? <equality>` goal block".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let to_prove_equal_fact =
            self.parse_goal_atomic_fact_block(&mut tb.body[0], "by extension")?;
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

        let mut proof: Vec<Stmt> = vec![];
        for block in tb.body[1..].iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }

        Ok(ByExtensionStmt::new(left, right, proof, tb.line_file.clone()).into())
    }
}
