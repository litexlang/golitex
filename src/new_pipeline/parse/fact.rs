use super::keywords::EQUAL;
use super::object::parse_obj;
use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact};
use crate::new_pipeline::ast::source_span::SourceSpan;
use crate::new_pipeline::ast::stmt::Stmt;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

impl Runtime {
    // Flat equality fact for now: `<obj> = <obj>` (obj = number | name, with `+`).
    pub(super) fn parse_fact_stmt(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        if !block.body.is_empty() {
            return Err(RuntimeError::Unsupported(
                "parse: indented fact bodies are not wired yet".to_string(),
            ));
        }

        let span = SourceSpan::new(block.line, block.source_path.clone());
        let tokens = &block.header;
        let mut i = 0;
        let left = parse_obj(tokens, &mut i, block)?;
        if i >= tokens.len() || tokens[i] != EQUAL {
            return Err(RuntimeParseError::new(
                "expected `=`",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }
        i += 1;
        let right = parse_obj(tokens, &mut i, block)?;
        if i != tokens.len() {
            return Err(RuntimeParseError::new(
                "trailing tokens",
                block.line,
                block.source_path.clone(),
            )
            .into());
        }

        let equal = EqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left,
            right,
            span,
        };
        Ok(Stmt::Fact(Fact::AtomicFact(AtomicFact::EqualFact(equal))))
    }
}
