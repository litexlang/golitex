use crate::error::ParsingError;
use crate::fact::Fact;
use crate::stmt::know_stmt::KnowStmt;
use crate::common::keywords::{COLON, COMMA, FORALL, KNOW};
use crate::execute::Executor;
use crate::stmt::Stmt;
use super::TokenBlock;

impl<'a> Executor<'a> {
    pub fn know_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(KNOW)?;
        if tb.current()? == COLON {
            tb.skip_token(COLON)?;
            let facts = self.parse_facts_in_body(tb)?;
            Ok(Stmt::KnowStmt(KnowStmt::new(facts, Some(tb.line_file_index))))
        } else if tb.current()? == FORALL {
            let fact = self.parse_fact(tb)?;
            Ok(Stmt::KnowStmt(KnowStmt::new(vec![fact], Some(tb.line_file_index))))
        } else {
            let mut facts: Vec<Fact> = vec![];
            loop {
                let o = self.parse_exist_or_and_chain_atomic_fact(tb)?;
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
