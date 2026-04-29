use crate::prelude::*;

impl Runtime {
    pub fn parse_by_for_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(FOR)?;
        if tb.current()? == RIGHT_ARROW {
            tb.skip_token(RIGHT_ARROW)?;
            let header = &tb.header;
            if header.len() < tb.parse_index + 2 || header.last().map(|t| t.as_str()) != Some(COLON)
            {
                return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for => ... : expected a forall fact and a trailing `:` on the same line".to_string(),
                    tb.line_file.clone(),
                ))));
            }
            let colon_pos = header.len() - 1;
            let fact_tokens = header[tb.parse_index..colon_pos].to_vec();
            if fact_tokens.is_empty() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by for => ... : expected a non-empty forall fact after `=>`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            let mut fact_tb = TokenBlock::new(fact_tokens, vec![], tb.line_file.clone());
            let fact = self.parse_fact(&mut fact_tb)?;
            if !fact_tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by for => ... : unfinished tokens in forall fact".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            tb.parse_index = colon_pos + 1;
            if !tb.exceed_end_of_head() {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by for => ... : unexpected tokens after `:`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }

            let forall_fact = match fact {
                Fact::ForallFact(ff) => ff,
                Fact::ForallFactWithIff(_) => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "by for: forall with `<=>` is not allowed here".to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "by for: shorthand after `=>` must be a single `forall` fact"
                                .to_string(),
                            tb.line_file.clone(),
                        ),
                    )));
                }
            };

            for g in forall_fact.params_def_with_type.groups.iter() {
                match &g.param_type {
                    ParamType::Obj(Obj::Range(_)) | ParamType::Obj(Obj::ClosedRange(_)) => {}
                    _ => {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_line_file(
                                "by for: each forall parameter type must be range or closed_range"
                                    .to_string(),
                                forall_fact.line_file.clone(),
                            ),
                        )));
                    }
                }
            }

            let names = forall_fact.params_def_with_type.collect_param_names();
            let lf = tb.line_file.clone();
            let proof: Vec<Stmt> = self.parse_stmts_with_optional_free_param_scope(
                ParamObjType::Forall,
                &names,
                lf,
                |this| {
                    tb.body
                        .iter_mut()
                        .map(|b| this.parse_stmt(b))
                        .collect::<Result<_, _>>()
                },
            )?;

            return Ok(ByForStmt::new(forall_fact, proof, tb.line_file.clone()).into());
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: expected `:` immediately after `for`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: expects a body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let prove_block = tb.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: expected prove block".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        if prove_block.header.get(0).map(|s| s.as_str()) != Some(PROVE) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: first block must be `prove:`".to_string(),
                    prove_block.line_file.clone(),
                ),
            )));
        }
        prove_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
        if prove_block.body.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: `prove:` must contain exactly one forall fact".to_string(),
                    prove_block.line_file.clone(),
                ),
            )));
        }

        let forall_block = prove_block.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by for: missing forall block".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        let fact = self.parse_fact(forall_block)?;
        let forall_fact = match fact {
            Fact::ForallFact(ff) => ff,
            Fact::ForallFactWithIff(_) => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by for: forall with `<=>` is not allowed here".to_string(),
                        forall_block.line_file.clone(),
                    ),
                )));
            }
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by for: `prove:` must be a single `forall` fact".to_string(),
                        forall_block.line_file.clone(),
                    ),
                )));
            }
        };

        for g in forall_fact.params_def_with_type.groups.iter() {
            match &g.param_type {
                ParamType::Obj(Obj::Range(_)) | ParamType::Obj(Obj::ClosedRange(_)) => {}
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file(
                            "by for: each forall parameter type must be range or closed_range"
                                .to_string(),
                            forall_fact.line_file.clone(),
                        ),
                    )));
                }
            }
        }

        let names = forall_fact.params_def_with_type.collect_param_names();
        let lf = tb.line_file.clone();
        let proof: Vec<Stmt> = self.parse_stmts_with_optional_free_param_scope(
            ParamObjType::Forall,
            &names,
            lf,
            |this| {
                tb.body
                    .iter_mut()
                    .skip(1)
                    .map(|b| this.parse_stmt(b))
                    .collect::<Result<_, _>>()
            },
        )?;

        Ok(ByForStmt::new(forall_fact, proof, tb.line_file.clone()).into())
    }
}
