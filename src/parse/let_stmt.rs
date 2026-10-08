use super::keywords::EQUAL;
use super::object::{is_simple_name, parse_obj};
use crate::ast::line_file::SourceLine;
use crate::ast::stmt::{DefineObjStmt, DefinitionStmt, LetObjStmt, Stmt};
use crate::runtime::{Runtime, RuntimeParseError, RuntimeResult};
use crate::tokenize::TokenBlock;

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
            RuntimeParseError::new(
                "`let` expects a name",
                block.line,
                block.source_path.clone(),
            )
        })?;
        if !is_simple_name(&name) {
            return Err(RuntimeParseError::new(
                format!("invalid let name `{name}`"),
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        // Occupy the name before parsing the value (allocates IdentifierId).
        let name = self.define_plain_atom_as_parse(&tb, name)?;

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

        Ok(Stmt::Definition(DefinitionStmt::DefineObj(
            DefineObjStmt::LetObjStmt(LetObjStmt {
                name,
                value,
                line_file: SourceLine::new(block.line, self.code_source.clone()),
            }),
        )))
    }
}
