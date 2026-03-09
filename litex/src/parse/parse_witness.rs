use crate::errors::ParsingError;
use crate::fact::ExistFact;
use crate::keywords::{COLON, EXIST, NONEMPTY_SET, WITNESS};
use super::Parser;
use crate::stmt::Stmt;
use super::TokenBlock;
use crate::stmt::witness_stmt::{WitnessExistFact, WitnessNonemptySet, WitnessStmt};

impl Parser {
    pub fn witness_stmt(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(WITNESS)?;
        if tb.current()? == EXIST {
            self.witness_exist_fact(tb)
        } else if tb.current()? == NONEMPTY_SET {
            self.witness_nonempty_set(tb) 
        } else {
            return Err(ParsingError::new("witness expects a exist or nonempty set", tb.line_file_index));
        }
    }

    pub fn witness_exist_fact(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(EXIST)?;
        let equal_tos = self.obj_list(tb)?;
        tb.skip_token(COLON)?;
        let exist_fact_result = self.exist_fact(tb, true)?;
        let exist_fact_in_witness = match exist_fact_result {
            ExistFact::TrueExistFact(t) => t,
            ExistFact::NotExistFact(_) => {
                return Err(ParsingError::new("witness exist expects a positive exist fact", tb.line_file_index));
            }
        };
        let mut proof = vec![];
        for block in tb.body.iter_mut() {
            proof.push(self.stmt(block)?);
        }
        Ok(Stmt::WitnessStmt(WitnessStmt::WitnessExistFact(WitnessExistFact::new(
            equal_tos,
            exist_fact_in_witness,
            proof,
            Some(tb.line_file_index),
        ))))
    }

    pub fn witness_nonempty_set(&self, tb: &mut TokenBlock) -> Result<Stmt, ParsingError> {
        tb.skip_token(NONEMPTY_SET)?;
        let obj = self.obj(tb)?;
        let set = self.obj(tb)?;
        let mut proof = vec![];
        for block in tb.body.iter_mut() {
            proof.push(self.stmt(block)?);
        }
        Ok(Stmt::WitnessStmt(WitnessStmt::WitnessNonemptySet(WitnessNonemptySet::new(
            obj,
            set,
            proof,
            Some(tb.line_file_index),
        ))))
    }
}
