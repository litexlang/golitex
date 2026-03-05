use crate::parser::Parser;
use crate::token_block::TokenBlock;
use crate::errors::ParsingError;
use crate::stmt::Stmt;
use crate::prove_stmt::ProveStmt;
use crate::keywords::{PROVE, COLON};

impl Parser {
    pub fn prove_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(PROVE)?;
        tb.skip_token(COLON)?;
        let mut proof = Vec::with_capacity(tb.body.len());
        for block in tb.body.iter_mut() {
            proof.push(self.stmt(block)?);
        }
        Ok(Stmt::ProveStmt(ProveStmt::new(proof, Some(tb.line_file_index))))
    }
}