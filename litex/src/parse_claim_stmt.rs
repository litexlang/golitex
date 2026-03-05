use crate::claim_stmt::{ClaimProveStmt, ClaimStmt};
use crate::fact::Fact;
use crate::forall_fact::ForallFact;
use crate::or_fact_or_and_fact_or_specific_fact::OrFactOrAndFactOrSpecFact;
use crate::specific_fact::SpecFact;
use crate::stmt::Stmt;
use crate::errors::ParsingError;
use crate::keywords::{CLAIM, COLON, COMMA, PROVE};
use crate::parser::Parser;
use crate::token_block::TokenBlock;

fn facts_to_then_facts(facts: Vec<Fact>) -> Vec<OrFactOrAndFactOrSpecFact> {
    facts
        .into_iter()
        .map(|f| match f {
            Fact::AtomicFact(a) => OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::AtomicFact(a)),
            Fact::ExistFact(e) => OrFactOrAndFactOrSpecFact::SpecFact(SpecFact::ExistFact(e)),
            Fact::OrFact(o) => OrFactOrAndFactOrSpecFact::OrFact(o),
            Fact::AndFact(a) => OrFactOrAndFactOrSpecFact::AndFact(a),
            Fact::ForallFact(_) | Fact::ForallFactWithIff(_) => {
                panic!("claim to_prove: forall fact not supported as list item")
            }
        })
        .collect()
}

impl Parser {
    pub fn claim_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(CLAIM)?;
        if tb.current()? == COLON {
            Ok(Stmt::ClaimStmt(self.multiline_facts_claim(tb)?))
        } else {
            Ok(Stmt::ClaimStmt(self.single_line_facts_claim(tb)?))
        }
    }

    /// claim : 多行；body 前若干块为 to_prove（每块一 fact），最后一块为 prove: 开头，其 body 为 proof。
    fn multiline_facts_claim(&self, tb: &mut TokenBlock) -> Result<ClaimStmt, ParsingError> {
        tb.skip_token(COLON)?;
        if tb.body.len() != 2 {
            return Err(ParsingError::new("claim : expects at least 2 body blocks", tb.line_file_index));
        }

        let to_prove = self.fact(&mut tb.body[0])?;
        let mut proof = Vec::new();
        let last = tb.body.last_mut().unwrap();
        last.skip_token_and_colon_and_exceed_end_of_head(PROVE)?;
        for block in last.body.iter_mut() {
            proof.push(self.stmt(block)?);
        }
        Ok(ClaimStmt::ClaimProveStmt(ClaimProveStmt::new(
            to_prove,
            proof,
            Some(tb.line_file_index),
        )))
    }

    /// claim fact, fact, ... : 单行 to_prove，然后 body 全是 proof stmt。
    fn single_line_facts_claim(&self, tb: &mut TokenBlock) -> Result<ClaimStmt, ParsingError> {
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