use super::super::keywords::{
    COLON, COMMA, EXIST, EXIST_BANG, FACT_PREFIX, FROM, IS_NONEMPTY_SET, LEFT_PAREN, RIGHT_PAREN,
    WITNESS,
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
    // witness exist|exist! … from objs [:]
    // witness $is_nonempty_set(S) from o [:]
    // witness $P(args) from objs [:]
    // Optional trailing `:` opens a local proof body (full Stmt list).
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
        // Stash proof blocks so `parse_exist_fact` does not see the witness body.
        let proof_blocks = std::mem::take(&mut tb.body);
        let exist_shaped_fact_in_witness = self.parse_exist_fact(tb)?;
        tb.expect(FROM)?;
        let mut equal_tos = vec![parse_obj(self, tb)?];
        while tb.peek() == Some(COMMA) {
            tb.advance()?;
            equal_tos.push(parse_obj(self, tb)?);
        }

        // Re-occupy exist binders so the local proof body can mention them
        // (legacy: parse_stmts_with_existing_free_param_bindings).
        // Example: `witness exist m R st {m = 0} from 0: m = 0`
        let params = exist_shaped_fact_in_witness.plain().typed_parameters.clone();
        let proof = self.with_forall_params_occupied(&params, block, |this| {
            this.parse_witness_optional_proof_body(tb, &proof_blocks, "witness exist")
        })?;

        Ok(Stmt::Witness(WitnessStmt::WitnessExistFact(
            WitnessExistFact {
                equal_tos,
                exist_shaped_fact_in_witness,
                proof,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }

    fn parse_witness_nonempty_set_header(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let proof_blocks = std::mem::take(&mut tb.body);
        tb.expect(FACT_PREFIX)?;
        tb.expect(IS_NONEMPTY_SET)?;
        tb.expect(LEFT_PAREN)?;
        let set = parse_obj(self, tb)?;
        tb.expect(RIGHT_PAREN)?;
        tb.expect(FROM)?;
        let obj = parse_obj(self, tb)?;

        let proof =
            self.parse_witness_optional_proof_body(tb, &proof_blocks, "witness $is_nonempty_set")?;

        Ok(Stmt::Witness(WitnessStmt::WitnessNonemptySet(
            WitnessNonemptySet {
                obj,
                set,
                proof,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }

    fn parse_witness_atomic_fact_header(
        &mut self,
        tb: &mut TokenBlock,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let proof_blocks = std::mem::take(&mut tb.body);
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

        let proof = self.parse_witness_optional_proof_body(tb, &proof_blocks, "witness `$P`")?;

        Ok(Stmt::Witness(WitnessStmt::WitnessAtomicFact(
            WitnessAtomicFact {
                atomic_fact,
                witnesses,
                proof,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            },
        )))
    }

    // Flat header => proof []. Trailing `:` => parse stashed indented body (may be empty).
    fn parse_witness_optional_proof_body(
        &mut self,
        tb: &mut TokenBlock,
        proof_blocks: &[TokenBlock],
        syntax_name: &str,
    ) -> RuntimeResult<Vec<Stmt>> {
        if tb.peek() == Some(COLON) {
            tb.expect(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error(format!(
                    "{syntax_name}: unexpected token after trailing `:`"
                )));
            }
            return self.parse_body_stmts(proof_blocks);
        }
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error(format!(
                "{syntax_name}: expected end of head or trailing `:`"
            )));
        }
        if !proof_blocks.is_empty() {
            return Err(tb.parse_error(format!(
                "{syntax_name}: indented body requires trailing `:` on the header"
            )));
        }
        Ok(vec![])
    }
}
