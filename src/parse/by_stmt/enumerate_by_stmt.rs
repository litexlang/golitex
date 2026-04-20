use crate::prelude::*;

impl Runtime {
    pub fn parse_by_enumerate_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ENUMERATE)?;
        if tb.current_token_is_equal_to(FINITE_SET) {
            tb.skip_token(FINITE_SET)?;
            tb.skip_token(COLON)?;
            return self.parse_by_enumerate_finite_set_stmt_forall_in_prove(tb);
        }
        if tb.current_token_is_equal_to(COLON) {
            return Err(RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by enumerate: expected `finite_set` before `:` (use `by enumerate finite_set:`)"
                    .to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            ))));
        }
        self.parse_by_enumerate_closed_range_stmt(tb)
    }

    /// `by enumerate finite_set:` then `prove:` with a single `forall` (list-set parameters, optional dom / `=>:`).
    fn parse_by_enumerate_finite_set_stmt_forall_in_prove(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "by enumerate finite_set: expected end of head after `:`".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "by enumerate finite_set: expects a body".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }

        let prove_block = tb.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by enumerate finite_set: expected prove block".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            )))
        })?;
        if prove_block.header.get(0).map(|s| s.as_str()) != Some(PROVE) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "by enumerate finite_set: first block must be `prove:`".to_string(),
                    prove_block.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }
        prove_block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
        if prove_block.body.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "by enumerate finite_set: `prove:` must contain exactly one forall fact"
                        .to_string(),
                    prove_block.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }

        let forall_block = prove_block.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by enumerate finite_set: missing forall block".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            )))
        })?;
        let fact = self.parse_fact(forall_block)?;
        let forall_fact = match fact {
            Fact::ForallFact(ff) => ff,
            Fact::ForallFactWithIff(_) => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "by enumerate finite_set: forall with `<=>` is not allowed here"
                            .to_string(),
                        forall_block.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
            _ => {
                return Err(RuntimeError::from(ParseRuntimeError(
                    RuntimeErrorStruct::new(
                        None,
                        "by enumerate finite_set: `prove:` must be a single `forall` fact"
                            .to_string(),
                        forall_block.line_file.clone(),
                        None,
                        vec![],
                    ),
                )));
            }
        };

        for g in forall_fact.params_def_with_type.groups.iter() {
            match &g.param_type {
                ParamType::Obj(Obj::ListSet(_)) => {}
                _ => {
                    return Err(RuntimeError::from(ParseRuntimeError(
                        RuntimeErrorStruct::new(
                            None,
                            "by enumerate finite_set: each forall parameter type must be a list set `{ ... }`"
                                .to_string(),
                            forall_fact.line_file.clone(),
                            None,
                            vec![],
                        ),
                    )));
                }
            }
        }

        let names = forall_fact.params_def_with_type.collect_param_names();
        let lf = tb.line_file.clone();
        let proof: Vec<Stmt> = self.parse_stmts_with_optional_free_param_scope(
            FreeParamObjType::Forall,
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
}
