use crate::stmt::claim_stmt::ClaimStmt;
use crate::fact::Fact;
use crate::stmt::Stmt;
use crate::error::ParsingError;
use crate::common::keywords::{CLAIM, COLON, RIGHT_ARROW};
use super::Parser;
use super::TokenBlock;

impl Parser {
    pub fn claim_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(CLAIM)?;
        if tb.current()? == COLON {
            Ok(Stmt::ClaimStmt(self.multiline_fact_claim(tb)?))
        } else {
            Ok(Stmt::ClaimStmt(self.single_line_fact_claim(tb)?))
        }
    }

    fn multiline_fact_claim(&self, tb: &mut TokenBlock) -> Result<ClaimStmt, ParsingError> {
        tb.skip_token(COLON)?;
        if tb.body.is_empty() {
            return Err(ParsingError::new("claim : expects at least one body block (=>: fact)", tb.line_file_index));
        }
        let fact = {
            let first = tb.body.get_mut(0).unwrap();
            first.parse_index = 0;
            first.skip_token_and_colon_and_exceed_end_of_head(RIGHT_ARROW)?;
            if first.body.len() != 1 {
                return Err(ParsingError::new("claim =>: expects exactly one body block (the fact)", first.line_file_index));
            }
            let f = self.parse_fact(first.body.get_mut(0).unwrap())?;
            if let Fact::ForallFactWithIff(_) = &f {
                return Err(ParsingError::new("claim multiline fact cannot be iff", first.line_file_index));
            }
            f
        };
        let proof: Vec<Stmt> = tb.body.iter_mut().skip(1).map(|b| self.parse_stmt(b)).collect::<Result<_, _>>()?;
        Ok(ClaimStmt::new(fact, proof, Some(tb.line_file_index)))
    }

    fn single_line_fact_claim(&self, tb: &mut TokenBlock) -> Result<ClaimStmt, ParsingError> {
        let fact = self.parse_exist_or_and_chain_atomic_fact(tb)?.to_fact();
        tb.skip_token(COLON)?;
        let mut proof = Vec::new();
        for block in tb.body.iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }
        Ok(ClaimStmt::new(fact, proof, Some(tb.line_file_index)))
    }
}