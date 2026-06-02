use crate::prelude::*;

impl Runtime {
    pub fn parse_by_axiom_of_choice_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(AXIOM_OF_CHOICE)?;
        if !tb.current_token_is_equal_to(COLON) {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by axiom_of_choice: expected `by axiom_of_choice: set S:`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        tb.skip_token(COLON)?;
        tb.skip_token(SET)?;
        let family = self.parse_obj(tb)?;
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by axiom_of_choice: expected end of head after trailing `:`".to_string(),
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
