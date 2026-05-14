use crate::prelude::*;

impl Runtime {
    pub fn parse_eval_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(EVAL)?;
        let lhs = self.parse_obj(tb)?;
        if !tb.exceed_end_of_head() && tb.current_token_is_equal_to(FROM) {
            tb.skip_token(FROM)?;
            let rhs = self.parse_obj(tb)?;
            return Ok(EvalByStmt::new(lhs, rhs, tb.line_file.clone()).into());
        }
        Ok(EvalStmt::new(lhs, tb.line_file.clone()).into())
    }
}
