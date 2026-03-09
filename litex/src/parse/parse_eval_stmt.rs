use crate::common::keywords::EVAL;
use super::Parser;
use super::TokenBlock;
use crate::error::ParsingError;
use crate::stmt::Stmt;
use crate::stmt::eval_stmt::EvalStmt;

impl Parser {
    pub fn eval_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(EVAL)?;
        let obj = self.obj(tb)?;
        Ok(Stmt::EvalStmt(EvalStmt::new(obj, Some(tb.line_file_index))))
    }
}