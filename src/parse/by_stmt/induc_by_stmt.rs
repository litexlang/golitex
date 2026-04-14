use crate::prelude::*;

impl Runtime {
    pub fn parse_by_induc_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(INDUC)?;
        let param = tb.advance()?;
        tb.skip_token(FROM)?;
        let induc_from = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(
                RuntimeError::new_parse_error_with_msg_position_previous_error(
                    "by induc: expected end of head".to_string(),
                    tb.line_file.clone(),
                    None,
                ),
            );
        }

        let mut to_prove: Vec<ExistOrAndChainAtomicFact> = vec![];
        for block in tb.body.iter_mut() {
            to_prove.push(self.parse_exist_or_and_chain_atomic_fact(block)?);
        }

        Ok(ByInducStmt::new(to_prove, param, induc_from, tb.line_file.clone()).into())
    }
}
