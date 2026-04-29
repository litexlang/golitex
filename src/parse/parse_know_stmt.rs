use crate::prelude::*;

impl Runtime {
    pub fn parse_know_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(KNOW)?;
        if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            let facts = self.parse_facts_in_body(tb)?;
            return Ok(KnowStmt::new(facts, tb.line_file.clone()).into());
        } else if tb.current_token_is_equal_to(FORALL) {
            let fact = self.parse_fact(tb)?;
            return Ok(KnowStmt::new(vec![fact], tb.line_file.clone()).into());
        } else if tb.current_token_is_equal_to(NOT) {
            if tb.token_at_add_index(1) == FORALL {
                let fact = self.parse_fact(tb)?;
                return Ok(KnowStmt::new(vec![fact], tb.line_file.clone()).into());
            }
        }

        let mut facts: Vec<Fact> = vec![];
        loop {
            let o = self.parse_exist_or_and_chain_atomic_fact(tb)?;
            facts.push(o.to_fact());

            if tb.exceed_end_of_head() {
                break;
            }
            tb.skip_token(COMMA)?;
        }
        Ok(KnowStmt::new(facts, tb.line_file.clone()).into())
    }
}
