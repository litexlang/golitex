use super::keywords::EQUAL;
use super::object::{is_simple_name, parse_obj};
use crate::new_pipeline::ast::source_span::SourceSpan;
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

        let tokens = &block.header;
        let mut i = 0;
        // leading `let` already matched by dispatch
        i += 1;

        let Some(name) = tokens.get(i).cloned() else {
            return Err(RuntimeParseError::new(
                "`let` expects a name",
                block.line,
                block.source_path.clone(),
            )
            .into());
        };
        if !is_simple_name(&name) {
            return Err(RuntimeParseError::new(
                format!("invalid let name `{name}`"),
                block.line,
                block.source_path.clone(),
            )
            .into());
        }
        i += 1;

        if tokens.get(i).map(String::as_str) != Some(EQUAL) {
            return Err(RuntimeParseError::new(
                "`let` expects `=` after the name",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }
        i += 1;

        let value = parse_obj(tokens, &mut i, block)?;
        if i != tokens.len() {
            return Err(RuntimeParseError::new(
                "trailing tokens after let value",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        self.occupy_name(name.clone()).map_err(|err| match err {
            crate::new_pipeline::runtime::RuntimeError::Invariant(message) => {
                RuntimeParseError::new(message, block.line, block.source_path.clone()).into()
            }
            other => other,
        })?;

        Ok(Stmt::Definition(DefinitionStmt::LetObjStmt(LetObjStmt {
            name,
            value,
            span: SourceSpan::new(block.line, block.source_path.clone()),
        })))
    }
}
