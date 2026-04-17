use crate::prelude::*;

impl Runtime {
    pub fn parse_by_enumerate_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ENUMERATE)?;
        if tb.current()? == CLOSED_RANGE {
            return self.parse_by_enumerate_closed_range_stmt(tb);
        }

        if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            return self.parse_by_enumerate_stmt_forall_in_prove(tb);
        }

        self.parse_by_enumerate_stmt_legacy_head(tb)
    }

    /// `by enumerate:` then `prove:` with a single `forall` (list-set parameters, optional dom / `=>:`).
    fn parse_by_enumerate_stmt_forall_in_prove(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "by enumerate: expected end of head after `:`".to_string(),
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
                    "by enumerate: expects a body".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }

        let prove_block = tb.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by enumerate: expected prove block".to_string(),
                tb.line_file.clone(),
                None,
                vec![],
            )))
        })?;
        if prove_block.header.get(0).map(|s| s.as_str()) != Some(PROVE) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "by enumerate: first block must be `prove:`".to_string(),
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
                    "by enumerate: `prove:` must contain exactly one forall fact".to_string(),
                    prove_block.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }

        let forall_block = prove_block.body.get_mut(0).ok_or_else(|| {
            RuntimeError::from(ParseRuntimeError(RuntimeErrorStruct::new(
                None,
                "by enumerate: missing forall block".to_string(),
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
                        "by enumerate: forall with `<=>` is not allowed here".to_string(),
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
                        "by enumerate: `prove:` must be a single `forall` fact".to_string(),
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
                            "by enumerate: each forall parameter type must be a list set `{ ... }`"
                                .to_string(),
                            forall_fact.line_file.clone(),
                            None,
                            vec![],
                        ),
                    )));
                }
            }
        }

        let mut proof: Vec<Stmt> = Vec::new();
        for b in tb.body.iter_mut().skip(1) {
            proof.push(self.parse_stmt(b)?);
        }

        Ok(ByEnumerateStmt::new(forall_fact, proof, tb.line_file.clone()).into())
    }

    /// `by enumerate` x `{1, 2},` … `:` — implicit forall, `prove:` lines are `then` facts only.
    fn parse_by_enumerate_stmt_legacy_head(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        let mut params: Vec<String> = vec![];
        let mut param_sets: Vec<ListSet> = vec![];
        while tb.current()? != COLON {
            params.push(tb.advance()?);
            param_sets.push(self.parse_list_set_obj(tb)?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "by enumerate: expected end of head after params".to_string(),
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
                    "by enumerate: expects prove: block and at least one body block".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }

        tb.body[0].skip_token_and_colon_and_exceed_end_of_head(PROVE)?;

        let mut to_prove: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        for block in tb.body[0].body.iter_mut() {
            to_prove.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        let mut params_def_with_type: Vec<ParamGroupWithParamType> = Vec::new();
        for (param_name, list_set_obj) in params.iter().zip(param_sets.iter()) {
            params_def_with_type.push(ParamGroupWithParamType::new(
                vec![param_name.clone()],
                ParamType::Obj(list_set_obj.clone().into()),
            ));
        }
        let forall_fact = ForallFact::new(
            ParamDefWithType::new(params_def_with_type),
            vec![],
            to_prove,
            tb.line_file.clone(),
        );

        let mut proof: Vec<Stmt> = vec![];
        for block in tb.body[1..].iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }

        Ok(ByEnumerateStmt::new(forall_fact, proof, tb.line_file.clone()).into())
    }
}
