use crate::error::ParsingError;
use crate::common::keywords::{COLON, EXIST, NONEMPTY_SET, WITNESS};
use crate::execute::Executor;
use crate::stmt::Stmt;
use super::TokenBlock;
use crate::stmt::witness_stmt::{WitnessExistFact, WitnessNonemptySet};

impl<'a> Executor<'a> {
    pub fn witness_stmt(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(WITNESS)?;
        if tb.current_token_is_equal_to(EXIST) {
            self.witness_exist_fact(tb)
        } else if tb.current_token_is_equal_to(NONEMPTY_SET) {
            self.witness_nonempty_set(tb) 
        } else {
            return Err(ParsingError::new("witness expects a exist or nonempty set".to_string(), tb.line_file, None));
        }
    }

    pub fn witness_exist_fact(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(EXIST)?;
        let equal_tos = self.parse_obj_list(tb)?;
        tb.skip_token(COLON)?;
        let exist_fact_in_witness = self.parse_exist_fact(tb)?;
        let mut proof = vec![];
        for block in tb.body.iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }
        Ok(Stmt::WitnessExistFact(WitnessExistFact::new(
            equal_tos,
            exist_fact_in_witness,
            proof,
            tb.line_file,
        )))
    }

    pub fn witness_nonempty_set(&mut self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(NONEMPTY_SET)?;
        let obj = self.parse_obj(tb)?;
        let set = self.parse_obj(tb)?;
        let mut proof = vec![];
        for block in tb.body.iter_mut() {
            proof.push(self.parse_stmt(block)?);
        }
        Ok(Stmt::WitnessNonemptySet(WitnessNonemptySet::new(
            obj,
            set,
            proof,
            tb.line_file,
        )))
    }
}
