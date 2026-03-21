use crate::common::keywords::EVAL;
use crate::execute::Executor;
use super::TokenBlock;
use crate::error::ParsingError;
use crate::stmt::Stmt;
use crate::stmt::eval_stmt::EvalStmt;

impl<'a> Executor<'a> {
    pub fn eval_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(EVAL)?;
        let obj = self.parse_obj(tb)?;
        Ok(Stmt::EvalStmt(EvalStmt::new(obj, tb.line_file)))
    }
}