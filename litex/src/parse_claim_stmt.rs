use crate::claim_stmt::{ClaimIffStmt, ClaimProveStmt, ClaimStmt};
use crate::fact::Fact;
use crate::stmt::Stmt;
use crate::errors::ParsingError;
use crate::keywords::{CLAIM, COLON, PROVE};
use crate::parser::Parser;
use crate::token_block::TokenBlock;

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
        if tb.body.len() < 2 {
            return Err(ParsingError::new("claim : expects at least 2 body blocks", tb.line_file_index));
        }

        let to_prove = self.fact(&mut tb.body[0])?;

        if let Fact::ForallFactWithIff(iff) = to_prove {
            if tb.body.len() != 3 {
                return Err(ParsingError::new("claim : iff expects 3 body blocks (to_prove, prove, prove)", tb.line_file_index));
            }
            let then_to_iff_proof = self.parse_prove_block(&mut tb.body[1])?;
            let iff_to_then_proof = self.parse_prove_block(&mut tb.body[2])?;
            Ok(ClaimStmt::ClaimIffStmt(ClaimIffStmt::new(
                iff,
                then_to_iff_proof,
                iff_to_then_proof,
                Some(tb.line_file_index),
            )))
        } else {
            if tb.body.len() != 2 {
                return Err(ParsingError::new("claim : prove expects 2 body blocks (to_prove, prove)", tb.line_file_index));
            }
            let proof = self.parse_prove_block(&mut tb.body[1])?;
            Ok(ClaimStmt::ClaimProveStmt(ClaimProveStmt::new(
                to_prove,
                proof,
                Some(tb.line_file_index),
            )))
        }
    }

    /// 解析一个 prove: 块，块头为 prove:，body 为 proof stmts。
    fn parse_prove_block(&self, block: &mut TokenBlock) -> Result<Vec<Stmt>, ParsingError> {
        block.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
        let mut proof = Vec::new();
        for b in block.body.iter_mut() {
            proof.push(self.stmt(b)?);
        }
        Ok(proof)
    }

    fn single_line_fact_claim(&self, tb: &mut TokenBlock) -> Result<ClaimStmt, ParsingError> {
        let to_prove = self.or_and_spec_fact(tb)?.to_fact();
        tb.skip_token(COLON)?;
        let mut proof = Vec::new();
        for block in tb.body.iter_mut() {
            proof.push(self.stmt(block)?);
        }
        Ok(ClaimStmt::ClaimProveStmt(ClaimProveStmt::new(
            to_prove,
            proof,
            Some(tb.line_file_index),
        )))
    }
}