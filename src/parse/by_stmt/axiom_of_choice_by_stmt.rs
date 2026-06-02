use crate::prelude::*;

impl Runtime {
    pub fn parse_by_axiom_of_choice_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(AXIOM_OF_CHOICE)?;
        let family = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by axiom_of_choice: expected end of head after `:`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let proof = tb
            .body
            .iter_mut()
            .map(|block| self.parse_stmt(block))
            .collect::<Result<_, _>>()?;

        Ok(ByAxiomOfChoiceStmt::new(family, proof, tb.line_file.clone()).into())
    }
}
