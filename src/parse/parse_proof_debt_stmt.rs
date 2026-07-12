use crate::prelude::*;

impl Runtime {
    pub fn parse_trust_fact_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        if tb.current_token_is_equal_to(COLON) {
            tb.skip_token(COLON)?;
            let facts = self.parse_facts_in_body(tb)?;
            return Ok(ProofDebtStmt::new(facts, tb.line_file.clone()).into());
        } else if tb.current_token_is_equal_to(FORALL) {
            let fact = self.parse_fact(tb)?;
            return Ok(ProofDebtStmt::new(vec![fact], tb.line_file.clone()).into());
        } else if tb.current_token_is_equal_to(NOT) {
            if tb.token_at_add_index(1) == FORALL {
                let fact = self.parse_fact(tb)?;
                return Ok(ProofDebtStmt::new(vec![fact], tb.line_file.clone()).into());
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
        Ok(ProofDebtStmt::new(facts, tb.line_file.clone()).into())
    }
}
