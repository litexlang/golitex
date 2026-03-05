use crate::errors::ParsingError;
use crate::keywords::{CLAIM, EXIST, FN, HAVE, KNOW, LET, PROP};
use crate::parser::Parser;
use crate::stmt::Stmt;
use crate::token_block::TokenBlock;

impl Parser {
    pub fn stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        match tb.current()? {
            PROP => self.def_prop_stmt(tb),
            LET => self.def_let_stmt(tb),
            HAVE => {
                if tb.token_at_index(1)? == FN {
                    self.have_fn_stmt(tb)
                } else if tb.token_at_index(1)? == EXIST {
                    self.have_exist(tb)
                } else {
                    self.have_obj_stmt(tb)
                }
            },
            KNOW => self.know_stmt(tb),
            CLAIM => self.claim_stmt(tb),
            _ => {
                let fact = self.fact(tb)?;
                Ok(Stmt::Fact(fact))
            }
        }
    }
}