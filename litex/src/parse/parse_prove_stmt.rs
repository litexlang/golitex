use crate::execute::Executor;
use super::TokenBlock;
use crate::error::ParsingError;
use crate::stmt::Stmt;
use crate::stmt::prove_stmt::ProveStmt;
use crate::common::keywords::{PROVE, COLON};

impl<'a> Executor<'a> {
    pub fn prove_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(PROVE)?;
        tb.skip_token(COLON)?;
        let mut proof = Vec::with_capacity(tb.body.len());
        for block in tb.body.iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }
        Ok(Stmt::ProveStmt(ProveStmt::new(proof, tb.line_file)))
    }
}