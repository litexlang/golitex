use super::super::keywords::{EXIST, FROM, OBTAIN};
use super::super::object::is_simple_name;
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{DefinitionStmt, ObtainObjFromExistFact, Stmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // obtain x, y from exist …   (other obtain forms → parse_error)
    pub(in super::super) fn parse_obtain_stmt(
        &mut self,
        block: &TokenBlock,
    ) -> RuntimeResult<Stmt> {
        let mut tb = block.clone();
        tb.expect(OBTAIN)?;

        let mut equal_tos = Vec::new();
        loop {
            if tb.peek() == Some(FROM) {
                break;
            }
            let name = tb
                .advance()
                .map_err(|_| tb.parse_error("`obtain` expects a name or `from`"))?;
            if !is_simple_name(&name) {
                return Err(tb.parse_error(format!("invalid obtain name `{name}`")));
            }
            equal_tos.push(name);
            if tb.peek() == Some(super::super::keywords::COMMA) {
                tb.advance()?;
            } else if tb.peek() != Some(FROM) {
                return Err(tb.parse_error("`obtain` expects `,` or `from` after each name"));
            }
        }
        if equal_tos.is_empty() {
            return Err(tb.parse_error("`obtain` expects at least one name before `from`"));
        }
        tb.expect(FROM)?;

        if tb.peek() != Some(EXIST) && tb.peek() != Some(super::super::keywords::EXIST_BANG) {
            return Err(tb.parse_error(
                "obtain: only `from exist` / `from exist!` is wired; other sources are not wired yet",
            ));
        }

        let fact = self.parse_exist_fact(&mut tb)?;
        if !tb.exceed_end_of_head() {
            return Err(tb.parse_error("trailing tokens after obtain exist fact"));
        }
        if !tb.body.is_empty() {
            return Err(tb.parse_error("obtain cannot have an indented body"));
        }

        for name in &equal_tos {
            self.define_plain_atom_as_parse(&tb, name.clone())?;
        }
        Ok(Stmt::Definition(DefinitionStmt::ObtainObjFromExistFact(
            ObtainObjFromExistFact {
                equal_tos,
                fact,
                line_file: LineFile::new(block.line, block.source_path.clone()),
            },
        )))
    }
}
