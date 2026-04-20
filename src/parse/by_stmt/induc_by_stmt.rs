use crate::prelude::*;

impl Runtime {
    pub fn parse_by_induc_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(INDUC)?;
        let param = tb.advance()?;

        tb.skip_token(FROM)?;
        let induc_from = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "by induc: expected end of head".to_string(),
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
                    "by induc: expects prove: block".to_string(),
                    tb.line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }

        tb.body[0].skip_token_and_colon_and_exceed_end_of_head(PROVE)?;

        if tb.body[0].body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new(
                    None,
                    "by induc prove: expects at least one fact to prove".to_string(),
                    tb.body[0].line_file.clone(),
                    None,
                    vec![],
                ),
            )));
        }

        let prove_line = tb.body[0].line_file.clone();
        let induc_param = [param.clone()];
        let mut to_prove: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        self.parse_in_local_free_param_scope(
            FreeParamObjType::Induc,
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
            FreeParamObjType::Induc,
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

        Ok(ByInducStmt::new(to_prove, param, induc_from, proof, tb.line_file.clone()).into())
    }
}
