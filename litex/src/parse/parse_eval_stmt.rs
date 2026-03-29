use super::TokenBlock;
use crate::prelude::*;

impl Runtime {
    pub fn parse_eval_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(EVAL)?;
        let obj = self.parse_obj(tb)?;
        Ok(Stmt::EvalStmt(EvalStmt::new(obj, tb.line_file)))
    }
}
