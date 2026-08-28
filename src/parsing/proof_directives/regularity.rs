use crate::prelude::*;

impl Runtime {
    pub fn parse_by_regularity_axiom_stmt(
        &mut self,
        tb: &mut TokenBlock,
    ) -> Result<Stmt, RuntimeError> {
        tb.skip_token(REGULARITY_AXIOM)?;
        let args = self.parse_braced_objs(tb)?;
        if args.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    format!(
                        "by regularity_axiom: expected exactly one set argument, got {}",
                        args.len()
                    ),
                    tb.line_file.clone(),
                ),
            )));
        }
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by regularity_axiom: unexpected token after argument".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByRegularityAxiomStmt::new(args[0].clone(), tb.line_file.clone()).into())
    }
}
