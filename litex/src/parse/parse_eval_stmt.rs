use super::TokenBlock;
use crate::common::keywords::EVAL;
use crate::error::ParsingError;
use crate::execute::Runtime;
use crate::stmt::eval_stmt::EvalStmt;
use crate::stmt::Stmt;

impl Runtime {
    pub fn parse_eval_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(EVAL)?;
        let obj = self.parse_obj(tb)?;
        Ok(Stmt::EvalStmt(EvalStmt::new(obj, tb.line_file)))
    }
}
