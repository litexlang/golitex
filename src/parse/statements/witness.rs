use super::super::keywords::{
    COMMA, EXIST, EXIST_BANG, FACT_PREFIX, FROM, IS_NONEMPTY_SET, LEFT_PAREN, RIGHT_PAREN, WITNESS,
};
use super::super::object::parse_obj;
use crate::ast::fact::AtomicFact;
use crate::ast::line_file::SourceLine;
use crate::ast::stmt::{
    Stmt, WitnessAtomicFact, WitnessExistFact, WitnessNonemptySet, WitnessStmt,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

impl Runtime {
    // witness exist|exist! … from objs
    // witness $is_nonempty_set(S) from o
    // witness $P(args) from objs
    // no indented proof body
    pub(in super::super) fn parse_witness_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(WITNESS)?;

        if tb.peek() == Some(EXIST) || tb.peek() == Some(EXIST_BANG) {
            return self.parse_witness_exist_fact_header(&mut tb, block);
        }
        if tb.peek() == Some(FACT_PREFIX) && tb.peek_at(1) == Some(IS_NONEMPTY_SET) {
            return self.parse_witness_nonempty_set_header(&mut tb, block);
        }
        if tb.peek() == Some(FACT_PREFIX) {
            return self.parse_witness_atomic_fact_header(&mut tb, block);
        }

        Err(tb.parse_error(
            "witness expects `exist` / `exist!`, `$is_nonempty_set(...)`, or `$P(...)`",
        ))
    }

    fn parse_witness_exist_fact_header(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let exist_shaped_fact_in_witness = self.parse_exist_fact(tb)?;
        tb.expect(FROM)?;
        let mut equal_tos = vec![parse_obj(self, tb)?];
        while tb.peek() == Some(COMMA) {
            tb.advance()?;
            equal_tos.push(parse_obj(self, tb)?);
        }

        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(
                "witness exist: unexpected tokens after witnesses; proof body is not supported",
            ));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error(
                "witness exist: indented proof body is not supported; prove obligations before witness",
            ));
        }

        Ok(Stmt::Witness(WitnessStmt::WitnessExistFact(
            WitnessExistFact {
                equal_tos,
                exist_shaped_fact_in_witness,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }

    fn parse_witness_nonempty_set_header(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        tb.expect(FACT_PREFIX)?;
        tb.expect(IS_NONEMPTY_SET)?;
        tb.expect(LEFT_PAREN)?;
        let set = parse_obj(self, tb)?;
        tb.expect(RIGHT_PAREN)?;
        tb.expect(FROM)?;
        let obj = parse_obj(self, tb)?;

        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(
                "witness $is_nonempty_set: unexpected tokens after witness object",
            ));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error(
                "witness $is_nonempty_set: indented proof body is not supported; prove membership before witness",
            ));
        }

        Ok(Stmt::Witness(WitnessStmt::WitnessNonemptySet(
            WitnessNonemptySet {
                obj,
                set,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }

    fn parse_witness_atomic_fact_header(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let atomic = self.parse_atomic_fact(tb, true)?;
        let AtomicFact::NormalAtomicFact(atomic_fact) = atomic else {
            return Err(tb.parse_error(
                "witness `$P`: expected a positive normal atomic prop fact",
            ));
        };
        tb.expect(FROM)?;
        let mut witnesses = vec![parse_obj(self, tb)?];
        while tb.peek() == Some(COMMA) {
            tb.advance()?;
            witnesses.push(parse_obj(self, tb)?);
        }

        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(
                "witness `$P`: unexpected tokens after witnesses; proof body is not supported",
            ));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error(
                "witness `$P`: indented proof body is not supported; prove obligations before witness",
            ));
        }

        Ok(Stmt::Witness(WitnessStmt::WitnessAtomicFact(
            WitnessAtomicFact {
                atomic_fact,
                witnesses,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }
}
