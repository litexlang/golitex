use crate::prelude::*;

impl Runtime {
    pub fn parse_by_zorn_lemma_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ZORN_LEMMA)?;
        if !tb.current_token_is_equal_to(COLON) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by zorn_lemma: expected `by zorn_lemma: set S, prop P:`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        tb.skip_token(COLON)?;
        tb.skip_token(SET)?;
        let set = self.parse_obj(tb)?;
        tb.skip_token(COMMA)?;
        tb.skip_token(PROP)?;
        let prop_name = self.parse_atomic_name(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by zorn_lemma: expected end of head after trailing `:`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let proof = tb
            .body
            .iter_mut()
            .map(|block| self.parse_stmt(block))
            .collect::<Result<_, _>>()?;

        Ok(ByZornLemmaStmt::new(set, prop_name, proof, tb.line_file.clone()).into())
    }
}
