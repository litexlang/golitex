use crate::prelude::*;

impl Runtime {
    pub fn parse_by_enumerate_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ENUMERATE)?;
        if tb.current_token_is_equal_to(FINITE_SET) {
            tb.skip_token(FINITE_SET)?;
            if tb.current()? != COLON {
                let (fact, has_proof_body) = self.parse_header_fact_with_optional_trailing_colon(
                    tb,
                    "by enumerate finite_set",
                    "by enumerate finite_set => <forall fact>:",
                    "by enumerate finite_set <forall fact>:",
                )?;
                let forall_fact = match fact {
                    Fact::ForallFact(ff) => ff,
                    Fact::ForallFactWithIff(_) => {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_line_file(
                                "by enumerate finite_set: forall with `<=>` is not allowed here"
                                    .to_string(),
                                tb.line_file.clone(),
                            ),
                        )));
                    }
                    _ => {
                        return Err(RuntimeError::from(ParseRuntimeError(
                            RuntimeErrorStruct::new_with_msg_and_line_file("by enumerate finite_set: header shorthand must be a single `forall` fact"
                                    .to_string(), tb.line_file.clone()),
                        )));
                    }
                };

                for g in forall_fact.params_def_with_type.groups.iter() {
                    match &g.param_type {
                        ParamType::Obj(Obj::ListSet(_)) => {}
                        _ => {
                            return Err(RuntimeError::from(ParseRuntimeError(
                                RuntimeErrorStruct::new_with_msg_and_line_file("by enumerate finite_set: each forall parameter type must be a list set `{ ... }`"
                                        .to_string(), forall_fact.line_file.clone()),
                            )));
                        }
                    }
                }

                let names = forall_fact.params_def_with_type.collect_param_names();
                let lf = tb.line_file.clone();
                let proof: Vec<Stmt> = if has_proof_body {
                    self.parse_stmts_with_optional_free_param_scope(
                        ParamObjType::Forall,
                        &names,
                        lf,
                        |this| {
                            tb.body
                                .iter_mut()
                                .map(|b| this.parse_stmt(b))
                                .collect::<Result<_, _>>()
                        },
                    )?
                } else {
                    vec![]
                };

                return Ok(
                    ByEnumerateFiniteSetStmt::new(forall_fact, proof, tb.line_file.clone()).into(),
                );
            }
            tb.skip_token(COLON)?;
            return self.parse_by_enumerate_finite_set_stmt_forall_in_prove(tb);
        }
        if tb.current_token_is_equal_to(RANGE) || tb.current_token_is_equal_to(CLOSED_RANGE) {
            return self.parse_by_enumerate_range_stmt(tb);
        }
        Err(RuntimeError::from(ParseRuntimeError(
            RuntimeErrorStruct::new_with_msg_and_line_file(
                "by enumerate: expected `finite_set`, `range`, or `closed_range` after `enumerate`"
                    .to_string(),
                tb.line_file.clone(),
            ),
        )))
    }

    /// `by enumerate finite_set:` then `prove:` with a single `forall` (list-set parameters, optional dom / `=>:`).
    fn parse_by_enumerate_finite_set_stmt_forall_in_prove(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by enumerate finite_set: expected end of head after `:`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by enumerate finite_set: expects a body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let prove_block = tb.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by enumerate finite_set: expected prove block".to_string(),
                    tb.line_file.clone(),
                ),
            ))
        })?;
        if prove_block.header.get(0).map(|s| s.as_str()) != Some(PROVE) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by enumerate finite_set: first block must be `prove:`".to_string(),
                    prove_block.line_file.clone(),
                ),
            )));
        }
        prove_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
        if prove_block.body.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by enumerate finite_set: `prove:` must contain exactly one forall fact"
                        .to_string(),
                    prove_block.line_file.clone(),
                ),
            )));
        }

        let forall_block = prove_block.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by enumerate finite_set: missing forall block".to_string(),
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
                        "by enumerate finite_set: forall with `<=>` is not allowed here"
                            .to_string(),
                        forall_block.line_file.clone(),
                    ),
                )));
            }
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by enumerate finite_set: `prove:` must be a single `forall` fact"
                            .to_string(),
                        forall_block.line_file.clone(),
                    ),
                )));
            }
        };

        for g in forall_fact.params_def_with_type.groups.iter() {
            match &g.param_type {
                ParamType::Obj(Obj::ListSet(_)) => {}
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new_with_msg_and_line_file("by enumerate finite_set: each forall parameter type must be a list set `{ ... }`"
                                .to_string(), forall_fact.line_file.clone()),
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

        Ok(ByEnumerateFiniteSetStmt::new(forall_fact, proof, tb.line_file.clone()).into())
    }

    fn parse_by_enumerate_range_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        let range_keyword = tb.current()?.to_string();
        tb.skip_token(range_keyword.as_str())?;
        tb.skip_token(COLON)?;

        let element = self.parse_obj(tb)?;
        tb.skip_token(FACT_PREFIX)?;
        tb.skip_token(IN)?;
        let range_obj = self.parse_obj(tb)?;
        let range = match (range_keyword.as_str(), range_obj) {
            (RANGE, Obj::Range(range)) => ClosedRangeOrRange::Range(range),
            (CLOSED_RANGE, Obj::ClosedRange(closed_range)) => {
                ClosedRangeOrRange::ClosedRange(closed_range)
            }
            (RANGE, _) => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by enumerate range: expected range(lo, hi) after `$in`".to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            (CLOSED_RANGE, _) => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new_with_msg_and_line_file(
                        "by enumerate closed_range: expected closed_range(lo, hi) or lo ... hi after `$in`"
                            .to_string(),
                        tb.line_file.clone(),
                    ),
                )));
            }
            _ => unreachable!(),
        };

        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "by enumerate {}: expected end of line after membership fact",
                        range_keyword
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByEnumerateRangeStmt::new(element, range, tb.line_file.clone()).into())
    }
}
