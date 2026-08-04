use crate::prelude::*;

impl Runtime {
    pub fn parse_by_def_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(DEF)?;
        if tb.current()? != COLON {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by def no longer accepts a goal on the header; use `by def:` followed by `? <fact>`"
                        .to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        tb.skip_token(COLON)?;
        if !tb.exceed_end_of_head() || tb.body.len() != 1 {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by def expects exactly one `? <fact>` goal block".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        let fact = self.parse_goal_atomic_fact_block(&mut tb.body[0], "by def")?;
        if !fact.is_true() {
            return Err(RuntimeError::from(ParseRuntimeError(
                RuntimeErrorStruct::new_with_msg_and_line_file(
                    "by def expects one positive atomic fact".to_string(),
                    tb.line_file.clone(),
                ),
            )));
        }
        Ok(ByDefStmt::new(fact, tb.line_file.clone()).into())
    }
}
