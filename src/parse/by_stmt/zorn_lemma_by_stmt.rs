use crate::prelude::*;

impl Runtime {
    pub fn parse_by_zorn_lemma_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(ZORN_LEMMA)?;
        let set = self.parse_obj(tb)?;
        tb.skip_token(FROM)?;
        let prop_name = self.parse_atomic_name(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by zorn_lemma: expected end of head after `:`".to_string(),
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
