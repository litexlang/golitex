use crate::prelude::*;

impl Runtime {
    pub fn parse_eval_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(EVAL)?;
        let obj = self.parse_obj(tb)?;
        Ok(EvalStmt::new(obj, tb.line_file.clone()).into())
    }
}
