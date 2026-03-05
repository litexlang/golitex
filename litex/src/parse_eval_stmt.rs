use crate::keywords::EVAL;
use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::errors::ParsingError;
use crate::stmt::Stmt;
use crate::eval_stmt::EvalStmt;

impl Parser {
    pub fn eval_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(EVAL)?;
        let obj = self.obj(tb)?;
        Ok(Stmt::EvalStmt(EvalStmt::new(obj, Some(tb.line_file_index))))
    }
}