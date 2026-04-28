use crate::prelude::*;

impl Runtime {
    pub fn parse_by_induc_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(INDUC)?;
        self.parse_induc_stmt_after_keyword(tb, false)
    }

    pub fn parse_strong_induc_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(STRONG_INDUC)?;
        self.parse_induc_stmt_after_keyword(tb, true)
    }

    fn parse_induc_stmt_after_keyword(
        &mut self,
        tb: &mut TokenBlock,
        strong: bool,
    ) -> Result<Stmt, RuntimeError> {
        let param = tb.advance()?;

        tb.skip_token(FROM)?;
        let induc_from = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "induc: expected end of head".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        if tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "induc: expects prove: block".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        tb.body[0].skip_token_and_colon_and_exceed_end_of_head(PROVE)?;

        if tb.body[0].body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "induc prove: expects at least one fact to prove".to_string(),
                    tb.body[0].line_file.clone(),
                ),
            )));
        }

        let prove_line = tb.body[0].line_file.clone();
        let induc_param = [param.clone()];
        let mut to_prove: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        self.parse_in_local_free_param_scope(
            ParamObjType::Induc,
            &induc_param,
            prove_line,
            |this| {
                for block in tb.body[0].body.iter_mut() {
                    to_prove.push(this.parse_exist_or_and_chain_atomic_fact(block)?);
                }
                Ok(())
            },
        )?;

        let proof_line = tb.line_file.clone();
        let proof: Vec<Stmt> = self.parse_stmts_with_optional_free_param_scope(
            ParamObjType::Induc,
            &induc_param,
            proof_line,
            |this| {
                tb.body
                    .iter_mut()
                    .skip(1)
                    .map(|b| this.parse_stmt(b))
                    .collect::<Result<_, _>>()
            },
        )?;

        Ok(
            ByInducStmt::new(
                to_prove,
                param,
                induc_from,
                proof,
                tb.line_file.clone(),
                strong,
            )
            .into(),
        )
    }
}
