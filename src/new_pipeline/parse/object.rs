use super::keywords::{
    ADD, DIV, LEFT_PAREN, MUL, RIGHT_PAREN, SUB,
};
use crate::new_pipeline::ast::obj::{Add, AtomObj, Div, Identifier, Mul, Number, Obj, Sub};
use crate::new_pipeline::runtime::{RuntimeParseError, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

pub fn parse_obj(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    parse_add_sub(tb)
}

fn parse_add_sub(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_mul_div(tb)?;
    while let Some(op) = tb.peek() {
        if op == ADD {
            tb.advance()?;
            let right = parse_mul_div(tb)?;
            left = Obj::Add(Add {
                left: Box::new(left),
                right: Box::new(right),
            });
        } else if op == SUB {
            tb.advance()?;
            let right = parse_mul_div(tb)?;
            left = Obj::Sub(Sub {
                left: Box::new(left),
                right: Box::new(right),
            });
        } else {
            break;
        }
    }
    Ok(left)
}

fn parse_mul_div(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_unary(tb)?;
    while let Some(op) = tb.peek() {
        if op == MUL {
            tb.advance()?;
            let right = parse_unary(tb)?;
            left = Obj::Mul(Mul {
                left: Box::new(left),
                right: Box::new(right),
            });
        } else if op == DIV {
            tb.advance()?;
            let right = parse_unary(tb)?;
            left = Obj::Div(Div {
                left: Box::new(left),
                right: Box::new(right),
            });
        } else {
            break;
        }
    }
    Ok(left)
}

fn parse_unary(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    if tb.peek() == Some(SUB) {
        tb.advance()?;
        let right = parse_unary(tb)?;
        // No Neg variant in AST yet; encode as `0 - right`.
        return Ok(Obj::Sub(Sub {
            left: Box::new(Obj::Number(Number {
                normalized_value: "0".to_string(),
            })),
            right: Box::new(right),
        }));
    }
    parse_primary(tb)
}

fn parse_primary(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let Some(token) = tb.peek().map(str::to_string) else {
        return Err(RuntimeParseError::new(
            "expected object",
            tb.line,
            tb.source_path.clone(),
        )
        .into());
    };

    if token == LEFT_PAREN {
        tb.advance()?;
        let inner = parse_obj(tb)?;
        tb.expect(RIGHT_PAREN)?;
        return Ok(inner);
    }

    if token.chars().all(|c| c.is_ascii_digit()) && !token.is_empty() {
        tb.advance()?;
        return Ok(Obj::Number(Number {
            normalized_value: token,
        }));
    }

    if is_atom_name(&token) {
        tb.advance()?;
        return Ok(Obj::Atom(AtomObj::Identifier(Identifier { name: token })));
    }

    Err(RuntimeParseError::new(
        format!("expected number or name, got `{token}`"),
        tb.line,
        tb.source_path.clone(),
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

pub fn is_atom_name(s: &str) -> bool {
    if is_simple_name(s) {
        return true;
    }
    matches!(
        s,
        "N+" | "Z+" | "Q+" | "R+" | "Z-" | "Q-" | "R-" | "Z*" | "Q*" | "R*" | "C*"
    )
}
