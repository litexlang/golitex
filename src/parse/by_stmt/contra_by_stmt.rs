use crate::prelude::*;

impl Runtime {
    /// `by contra:` then a `prove:` or `?` goal block, optional proof statements, then `impossible` atomic fact.
    ///
    /// Shorthand: `by contra goal:` embeds the goal on the header line; body is optional proof
    /// statement blocks followed by `impossible ...` as the last block.
    pub fn parse_by_contra_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(CONTRA)?;
        if tb.current()? == RIGHT_ARROW {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by contra: use `by contra <goal>:` instead of `by contra => <goal>:`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let (to_prove, inline_goal): (Fact, bool) = if tb.current()? != COLON {
            let header = &tb.header;
            if header.len() < tb.parse_index + 2 || header.last().map(|t| t.as_str()) != Some(COLON)
            {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by contra ... : expected one goal and a trailing `:` on the same line"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let colon_pos = header.len() - 1;
            let fact_tokens = header[tb.parse_index..colon_pos].to_vec();
            if fact_tokens.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by contra ... : expected a non-empty goal after `by contra`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut fact_tb = TokenBlock::new(fact_tokens, vec![], tb.line_file.clone());
            let fact = self.parse_fact(&mut fact_tb)?;
            if !fact_tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by contra ... : unfinished tokens in goal".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            tb.parse_index = colon_pos + 1;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by contra ... : unexpected tokens after `:`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            (fact, true)
        } else {
            tb.skip_token(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by contra: expected end of head after by contra:".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            if tb.body.len() < 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by contra: expects `prove:` or `?` goal block and impossible ... tail"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let to_prove = {
                let goal_block = tb.body.get_mut(0).ok_or_else(|| {
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "Expected body".to_string(),
                            tb.line_file.clone(),
                        ),
                    ))
                })?;
                self.parse_goal_fact_block(goal_block, "by contra")?
            };
            (to_prove, false)
        };

        let n = tb.body.len();
        if inline_goal {
            if n < 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by contra ... : expects a final `impossible ...` block in the body"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
        } else if n < 2 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by contra: expects `prove:` or `?` goal block and impossible ... tail"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let proof_hi = n.saturating_sub(1);
        let proof_lo = if inline_goal { 0 } else { 1 };
        let mut proof = Vec::new();
        if proof_lo < proof_hi {
            for block in tb.body[proof_lo..proof_hi].iter_mut() {
                proof.push(self.parse_stmt(block)?);
            }
        }
        let mut last_block = tb.body.last_mut().ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "Expected body".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        last_block.skip_token(IMPOSSIBLE)?;
        let impossible_fact = self.parse_atomic_fact(&mut last_block, true)?;
        Ok(ByContraStmt::new(to_prove, proof, impossible_fact, tb.line_file.clone()).into())
    }
}
