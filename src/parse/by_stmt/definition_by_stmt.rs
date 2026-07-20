use crate::prelude::*;

impl Runtime {
    pub fn parse_by_def_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(DEF)?;
        if !tb.body.is_empty() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by def is a single-line statement and does not accept a body".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }

        let fact = self.parse_atomic_fact(tb, true)?;
        let AtomicFact::NormalAtomicFact(fact) = fact else {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by def expects one positive concrete prop fact such as `$P(a, b)`".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        };
        if !tb.exceed_end_of_head() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by def is a single-line statement and does not accept trailing tokens or `:`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByDefStmt::new(fact, tb.line_file.clone()).into())
    }
}
