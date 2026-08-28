//! Trusted source statements.

use crate::prelude::*;

impl Runtime {
    pub fn parse_trust_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, RuntimeError> {
        tb.skip_token(TRUST)?;
        if tb.current_token_is_equal_to(HAVE) {
            return self.parse_trust_have_stmt(tb);
        }
        self.parse_trust_fact_stmt(tb)
    }
}
