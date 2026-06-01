use crate::prelude::*;

impl Runtime {
    /// `by extension:` then `prove:` with exactly one equality, plus proof blocks.
    ///
    /// Shorthand: `by extension A = B:` puts the goal on the header line; body is only proof blocks.
    /// If no proof blocks are needed, `by extension A = B` may omit the trailing colon.
    pub fn parse_by_extension_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(EXTENSION)?;

        let (left, right, proof_lo): (Obj, Obj, usize) = if tb.current()? != COLON {
            let header = &tb.header;
            let has_trailing_colon = header.last().map(|t| t.as_str()) == Some(COLON);
            let equality_end = if has_trailing_colon {
                header.len() - 1
            } else {
                header.len()
            };
            if equality_end < tb.parse_index + 2 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by extension ... : expected one set equality on the same line".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let fact_tokens = header[tb.parse_index..equality_end].to_vec();
            if fact_tokens.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by extension ... : expected a non-empty equality after `by extension`"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut fact_tb = TokenBlock::new(fact_tokens, vec![], tb.line_file.clone());
            let to_prove_equal_fact = self.parse_atomic_fact(&mut fact_tb, true)?;
            if !fact_tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by extension ... : unfinished tokens in equality".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let (left, right) = match to_prove_equal_fact {
                AtomicFact::EqualFact(equal_fact) => (equal_fact.left, equal_fact.right),
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "by extension ... : expected set equality (`=` between two expressions)"
                                .to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            };
            tb.parse_index = equality_end;
            if has_trailing_colon {
                tb.skip_token(COLON)?;
            }
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by extension ... : unexpected tokens after `:`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            (left, right, 0)
        } else {
            tb.skip_token(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by extension: expected end of head after `by extension:`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            if tb.body.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by extension: expects at least one body block".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }

            tb.body[0].skip_token_and_colon_and_exceed_end_of_head(PROVE)?;

            if tb.body[0].body.len() != 1 {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by extension: prove: expects exactly one atomic fact block".to_string(),
                        tb.body[0].line_file.clone(),
                    ),
                )));
            }

            let to_prove_equal_fact = self.parse_atomic_fact(
                tb.body[0].body.get_mut(0).ok_or_else(|| {
                    RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "Expected body".to_string(),
                            tb.line_file.clone(),
                        ),
                    ))
                })?,
                true,
            )?;

            let (left, right) = match to_prove_equal_fact {
                AtomicFact::EqualFact(equal_fact) => (equal_fact.left, equal_fact.right),
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "by extension: prove: expects equal fact".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            };
            (left, right, 1)
        };

        let mut proof: Vec<Stmt> = vec![];
        for block in tb.body[proof_lo..].iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }

        Ok(ByExtensionStmt::new(left, right, proof, tb.line_file.clone()).into())
    }
}
