use crate::error::ParsingError;
use crate::fact::Fact;
use crate::stmt::know_stmt::KnowStmt;
use crate::common::keywords::{COLON, COMMA, FORALL, KNOW};
use super::Parser;
use crate::stmt::Stmt;
use super::TokenBlock;

impl Parser {
    pub fn know_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(KNOW)?;
        if tb.current()? == COLON {
            tb.skip_token(COLON)?;
            let facts = self.parse_facts_in_body(tb)?;
            Ok(Stmt::KnowStmt(KnowStmt::new(facts, Some(tb.line_file_index))))
        } else if tb.current()? == FORALL {
            let fact = self.fact(tb)?;
            Ok(Stmt::KnowStmt(KnowStmt::new(vec![fact], Some(tb.line_file_index))))
        } else {
            let mut facts: Vec<Fact> = vec![];
            loop {
                let o = self.or_and_spec_fact(tb)?;
                facts.push(o.to_fact());
                if tb.current()? != COMMA {
                    break;
                }
                tb.skip_token(COMMA)?;
            }
            Ok(Stmt::KnowStmt(KnowStmt::new(facts, Some(tb.line_file_index))))
        }
    }
}
