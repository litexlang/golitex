use super::keywords::ADD;
use crate::new_pipeline::ast::obj::{Add, AtomObj, Identifier, Number, Obj};
use crate::new_pipeline::runtime::{RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

pub fn parse_obj(
    tokens: &[String],
    i: &mut usize,
    block: &TokenBlock,
) -> RuntimeResult<Obj> {
    parse_add_expr(tokens, i, block)
}

fn parse_add_expr(
    tokens: &[String],
    i: &mut usize,
    block: &TokenBlock,
) -> RuntimeResult<Obj> {
    let mut left = parse_primary(tokens, i, block)?;
    while *i < tokens.len() && tokens[*i] == ADD {
        *i += 1;
        let right = parse_primary(tokens, i, block)?;
        left = Obj::Add(Add {
            left: Box::new(left),
            right: Box::new(right),
        });
    }
    Ok(left)
}

fn parse_primary(
    tokens: &[String],
    i: &mut usize,
    block: &TokenBlock,
) -> RuntimeResult<Obj> {
    let Some(token) = tokens.get(*i) else {
        return Err(RuntimeParseError::new(
            "expected object",
            block.line,
            block.source_path.clone(),
        )
        .into());
    };

    if token.chars().all(|c| c.is_ascii_digit()) && !token.is_empty() {
        *i += 1;
        return Ok(Obj::Number(Number {
            normalized_value: token.clone(),
        }));
    }

    if is_simple_name(token) {
        *i += 1;
        return Ok(Obj::Atom(AtomObj::Identifier(Identifier {
            name: token.clone(),
        })));
    }

    Err(RuntimeParseError::new(
        format!("expected number or name, got `{token}`"),
        block.line,
        block.source_path.clone(),
    )
    .into())
}

pub fn is_simple_name(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}
