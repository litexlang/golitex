use super::keywords::EQUAL;
use super::object::{is_simple_name, parse_obj};
use crate::new_pipeline::ast::line_file::LineFile;
use crate::new_pipeline::ast::stmt::{DefinitionStmt, LetObjStmt, Stmt};
use crate::new_pipeline::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // `let name = <obj>`
    pub(super) fn parse_let_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        if !block.body.is_empty() {
            return Err(RuntimeParseError::new(
                "`let` cannot have an indented body",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        let mut tb = block.clone();
        tb.advance()?; // `let`

        let name = tb.advance().map_err(|_| {
            RuntimeParseError::new("`let` expects a name", block.line, block.source_path.clone())
        })?;
        if !is_simple_name(&name) {
            return Err(RuntimeParseError::new(
                format!("invalid let name `{name}`"),
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        // Allocate atom id at definition time, before parsing the value.
        let identifier = self.define_plain_atom_as_parse(&tb, name)?;

        tb.expect(EQUAL).map_err(|_| {
            RuntimeParseError::new(
                "`let` expects `=` after the name",
                block.line,
                block.source_path.clone(),
            )
        })?;

        let value = parse_obj(self, &mut tb)?;
        if !tb.exceed_end_of_head() {
            return Err(RuntimeParseError::new(
                "trailing tokens after let value",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        Ok(Stmt::Definition(DefinitionStmt::LetObjStmt(LetObjStmt {
            name: identifier.name,
            atom_id: identifier.atom_id,
            value,
            line_file: LineFile::new(block.line, block.source_path.clone()),
        })))
    }
}
