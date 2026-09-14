use super::super::keywords::{COLON, EXIST, FROM, WITNESS};
use super::super::object::parse_obj;
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{Stmt, WitnessExistFact, WitnessStmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // witness exist … from objs [: proof]
    // other witness forms → clear parse_error
    pub(in super::super) fn parse_witness_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(WITNESS)?;
        if tb.peek() != Some(EXIST) && tb.peek() != Some(super::super::keywords::EXIST_BANG) {
            return Err(tb.parse_error(
                "witness: only `witness exist … from …` is wired; other forms are not wired yet",
            ));
        }

        let exist_fact_in_witness = self.parse_exist_fact(&mut tb)?;
        tb.expect(FROM)?;
        let mut equal_tos = vec![parse_obj(self, &mut tb)?];
        while tb.peek() == Some(super::super::keywords::COMMA) {
            tb.advance()?;
            equal_tos.push(parse_obj(self, &mut tb)?);
        }

        let proof = if tb.exceed_end_of_head() {
            if !tb.body.is_empty() {
                return Err(tb.parse_error(
                    "witness exist: indented proof body requires `:` at end of header",
                ));
            }
            Vec::new()
        } else {
            tb.expect(COLON)?;
            if !tb.exceed_end_of_head() {
                return Err(tb.parse_error("witness exist: unexpected tokens after `:` in header"));
            }
            let params = match &exist_fact_in_witness {
                crate::new_pipeline::ast::fact::ExistFact::PlainExistFact(b)
                | crate::new_pipeline::ast::fact::ExistFact::ExistUniqueFact(b)
                | crate::new_pipeline::ast::fact::ExistFact::NotExistFact(b) => &b.typed_parameters,
            };
            self.with_forall_params_occupied(params, &tb, |this| this.parse_body_stmts(&tb.body))?
        };

        Ok(Stmt::Witness(WitnessStmt::WitnessExistFact(
            WitnessExistFact {
                equal_tos,
                exist_fact_in_witness,
                proof,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }
}
