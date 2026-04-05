use crate::prelude::*;

impl Runtime {
    pub fn parse_by_enumerate_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ENUMERATE)?;
        let mut params: Vec<String> = vec![];
        let mut param_sets: Vec<ListSet> = vec![];
        if tb.current_token_is_equal_to(COLON) {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "by enumerate: expects at least one (param, set) pair".to_string(),
                tb.line_file.clone(),
                None,
            ));
        }
        while tb.current()? != COLON {
            params.push(tb.advance()?);
            param_sets.push(self.parse_list_set_obj(tb)?);
            if tb.current_token_is_equal_to(COMMA) {
                tb.skip_token(COMMA)?;
            }
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "by enumerate: expected end of head after params".to_string(),
                tb.line_file.clone(),
                None,
            ));
        }
        if tb.body.is_empty() {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "by enumerate: expects prove: block and at least one fact to prove".to_string(),
                tb.line_file.clone(),
                None,
            ));
        }

        if tb.body.is_empty() {
            return Err(RuntimeError::new_parse_error_with_msg_position_previous_error(
                "by enumerate: expects at least one body block".to_string(),
                tb.line_file.clone(),
                None,
            ));
        }

        tb.body[0].skip_token_and_colon_and_exceed_end_of_head(PROVE)?;

        let mut to_prove: Vec<ExistOrAndChainAtomicFact> = Vec::new();
        for block in tb.body[0].body.iter_mut() {
            to_prove.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        let mut proof: Vec<Stmt> = vec![];
        for block in tb.body[1..].iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }

        Ok(Stmt::ByEnumerateStmt(ByEnumerateStmt::new(
            params,
            param_sets,
            to_prove,
            proof,
            tb.line_file.clone(),
        )))
    }
}
