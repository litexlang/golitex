use crate::new_pipeline::runtime::{RuntimeError, RuntimeResult, Runtime};
use crate::new_pipeline::tokenize::TokenBlock;
use crate::prelude::*;
use std::rc::Rc;

impl Runtime {
    /// Parse token blocks into statements.
    ///
    /// Tracer: equality facts with `+` of numbers, e.g. `1 + 1 = 2`.
    pub fn parse(&mut self, token_blocks: &[TokenBlock]) -> RuntimeResult<Vec<Stmt>> {
        let mut stmts = Vec::new();
        for block in token_blocks {
            stmts.push(self.parse_token_block(block)?);
        }
        Ok(stmts)
    }

    fn parse_token_block(&mut self, block: &TokenBlock) -> RuntimeResult<Stmt> {
        if !block.body.is_empty() {
            return Err(RuntimeError::Unsupported(
                "parse: indented blocks are not wired yet".to_string(),
            ));
        }

        let line_file = (block.line, Rc::from(block.source_path.to_string()));
        let tokens = &block.header;
        let mut i = 0;
        let left = parse_add_expr(tokens, &mut i)?;
        if i >= tokens.len() || tokens[i] != "=" {
            return Err(RuntimeError::InvalidArguments(format!(
                "parse: expected `=` at line {} in {}",
                block.line, block.source_path
            )));
        }
        i += 1;
        let right = parse_add_expr(tokens, &mut i)?;
        if i != tokens.len() {
            return Err(RuntimeError::InvalidArguments(format!(
                "parse: trailing tokens at line {} in {}",
                block.line, block.source_path
            )));
        }

        let fact_id = crate::fact::id::FactId::new(self.ids.allocate_fact_id().value());
        let equal = EqualFact {
            fact_id,
            left,
            right,
            line_file,
        };
        let fact: Fact = equal.into();
        Ok(fact.into())
    }
}

fn parse_add_expr(tokens: &[String], i: &mut usize) -> RuntimeResult<Obj> {
    let mut left = parse_number(tokens, i)?;
    while *i < tokens.len() && tokens[*i] == "+" {
        *i += 1;
        let right = parse_number(tokens, i)?;
        left = Add::new(left, right).into();
    }
    Ok(left)
}

fn parse_number(tokens: &[String], i: &mut usize) -> RuntimeResult<Obj> {
    let Some(token) = tokens.get(*i) else {
        return Err(RuntimeError::InvalidArguments(
            "parse: expected number".to_string(),
        ));
    };
    if !token.chars().all(|c| c.is_ascii_digit()) {
        return Err(RuntimeError::InvalidArguments(format!(
            "parse: expected number, got `{token}`"
        )));
    }
    *i += 1;
    Ok(Number::new(token.clone()).into())
}
