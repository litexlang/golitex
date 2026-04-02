use crate::prelude::*;

impl Runtime {
    pub fn parse_prove_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(PROVE)?;
        tb.skip_token(COLON)?;
        self.push_parsing_time_name_scope();
        let result = self.parse_prove_stmt_body(tb);
        self.pop_parsing_time_name_scope();
        match result {
            Ok(proof) => Ok(Stmt::ProveStmt(ProveStmt::new(proof, tb.line_file.clone()))),
            Err(e) => Err(e),
        }
    }

    fn parse_prove_stmt_body(&mut self, tb: &mut TokenBlock) -> Result<Vec<Stmt>, ParsingError> {
        let mut proof = Vec::with_capacity(tb.body.len());
        for block in tb.body.iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }
        Ok(proof)
    }
}
