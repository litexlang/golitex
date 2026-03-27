use super::TokenBlock;
use crate::common::keywords::{COLON, COMMA, FORALL, KNOW};
use crate::error::ParsingError;
use crate::execute::Runtime;
use crate::fact::Fact;
use crate::stmt::know_stmt::KnowStmt;
use crate::stmt::Stmt;

impl Runtime {
    pub fn know_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(KNOW)?;
        if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            let facts = self.parse_facts_in_body(tb)?;
            Ok(Stmt::KnowStmt(KnowStmt::new(facts, tb.line_file)))
        } else if tb.current_token_is_equal_to(FORALL) {
            let fact = self.parse_fact(tb)?;
            Ok(Stmt::KnowStmt(KnowStmt::new(vec![fact], tb.line_file)))
        } else {
            let mut facts: Vec<Fact> = vec![];
            loop {
                let o = self.parse_exist_or_and_chain_atomic_fact(tb)?;
                facts.push(o.to_fact());

                if tb.exceed_end_of_head() {
                    break;
                }
                tb.skip_token(COMMA)?;
            }
            Ok(Stmt::KnowStmt(KnowStmt::new(facts, tb.line_file)))
        }
    }
}
