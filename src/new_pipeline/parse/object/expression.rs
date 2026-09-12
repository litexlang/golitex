use super::primary::{fn_obj_head_from_obj, parse_primary};
use crate::new_pipeline::ast::obj::{
    Add, Cart, ClosedRange, Div, FnObj, Intersect, Mod, Mul, Number, Obj,
    ObjAsStructInstanceWithFieldAccess, ObjAtIndex, Pow, Sub, Union,
};
use crate::new_pipeline::parse::keywords::{
    ADD, DIV, DOT, DOT_DOT_DOT, LEFT_BRACKET, LEFT_PAREN, MOD_OP, MUL, POW, RIGHT_BRACKET, SUB,
    UNICODE_CART, UNICODE_INTERSECT, UNICODE_UNION,
};
use crate::new_pipeline::runtime::RuntimeResult;
use crate::new_pipeline::tokenize::TokenBlock;

pub fn parse_obj(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    parse_unicode_union(tb)
}

fn parse_unicode_union(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_unicode_intersect(tb)?;
    while tb.peek() == Some(UNICODE_UNION) {
        tb.advance()?;
        let right = parse_unicode_intersect(tb)?;
        left = Obj::Union(Union {
            left: Box::new(left),
            right: Box::new(right),
        });
    }
    Ok(left)
}

fn parse_unicode_intersect(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_unicode_cart(tb)?;
    while tb.peek() == Some(UNICODE_INTERSECT) {
        tb.advance()?;
        let right = parse_unicode_cart(tb)?;
        left = Obj::Intersect(Intersect {
            left: Box::new(left),
            right: Box::new(right),
        });
    }
    Ok(left)
}

fn parse_unicode_cart(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let first = parse_add_sub(tb)?;
    if tb.peek() != Some(UNICODE_CART) {
        return Ok(first);
    }
    let mut factors = vec![first];
    while tb.peek() == Some(UNICODE_CART) {
        tb.advance()?;
        factors.push(parse_add_sub(tb)?);
    }
    Ok(Obj::Cart(Cart {
        args: factors.into_iter().map(Box::new).collect(),
    }))
}

fn parse_add_sub(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_mul_div_mod(tb)?;
    loop {
        match tb.peek() {
            Some(ADD) => {
                tb.advance()?;
                let right = parse_mul_div_mod(tb)?;
                left = Obj::Add(Add {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            Some(SUB) => {
                tb.advance()?;
                let right = parse_mul_div_mod(tb)?;
                left = Obj::Sub(Sub {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            _ => return Ok(left),
        }
    }
}

fn parse_mul_div_mod(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_closed_range(tb)?;
    loop {
        match tb.peek() {
            Some(MUL) => {
                tb.advance()?;
                let right = parse_closed_range(tb)?;
                left = Obj::Mul(Mul {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            Some(DIV) => {
                tb.advance()?;
                let right = parse_closed_range(tb)?;
                left = Obj::Div(Div {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            Some(MOD_OP) => {
                tb.advance()?;
                let right = parse_closed_range(tb)?;
                left = Obj::Mod(Mod {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            _ => return Ok(left),
        }
    }
}

fn parse_closed_range(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let left = parse_unary(tb)?;
    if tb.peek() == Some(DOT_DOT_DOT) {
        tb.advance()?;
        let right = parse_add_sub(tb)?;
        Ok(Obj::ClosedRange(ClosedRange {
            start: Box::new(left),
            end: Box::new(right),
        }))
    } else {
        Ok(left)
    }
}

fn parse_unary(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    if tb.peek() == Some(SUB) {
        tb.advance()?;
        let right = parse_unary(tb)?;
        // Encode unary minus as `0 - right` (no Neg variant).
        return Ok(Obj::Sub(Sub {
            left: Box::new(Obj::Number(Number {
                normalized_value: "0".to_string(),
            })),
            right: Box::new(right),
        }));
    }
    parse_pow(tb)
}

fn parse_pow(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let left = parse_postfix(tb)?;
    if tb.peek() == Some(POW) {
        tb.advance()?;
        // Right-associative: a^b^c = a^(b^c); right side re-enters unary.
        let right = parse_unary(tb)?;
        Ok(Obj::Pow(Pow {
            base: Box::new(left),
            exponent: Box::new(right),
        }))
    } else {
        Ok(left)
    }
}

fn parse_postfix(tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_primary(tb)?;
    left = parse_field_and_call_postfixes(tb, left)?;
    loop {
        if tb.peek() != Some(LEFT_BRACKET) {
            break;
        }
        tb.advance()?;
        let index = parse_obj(tb)?;
        tb.expect(RIGHT_BRACKET)?;
        left = Obj::ObjAtIndex(ObjAtIndex {
            obj: Box::new(left),
            index: Box::new(index),
        });
        left = parse_field_and_call_postfixes(tb, left)?;
    }
    Ok(left)
}

fn parse_field_and_call_postfixes(tb: &mut TokenBlock, mut result: Obj) -> RuntimeResult<Obj> {
    loop {
        if tb.peek() == Some(DOT) {
            tb.advance()?;
            let field_name = tb.advance()?;
            if !super::primary::is_simple_name(&field_name) {
                return Err(tb.parse_error(format!(
                    "expected field name after `.`, got `{field_name}`"
                )));
            }
            result = Obj::ObjAsStructInstanceWithFieldAccess(ObjAsStructInstanceWithFieldAccess {
                obj: Box::new(result),
                field_name,
                resolved_struct_carrier: None,
            });
            continue;
        }

        if tb.peek() == Some(LEFT_PAREN) {
            let Some(head) = fn_obj_head_from_obj(result.clone()) else {
                return Ok(result);
            };
            let mut body_vectors = Vec::new();
            while tb.peek() == Some(LEFT_PAREN) {
                let args = super::primary::parse_obj_list_paren(tb)?;
                body_vectors.push(args.into_iter().map(Box::new).collect());
            }
            result = Obj::FnObj(FnObj {
                head: Box::new(head),
                body: body_vectors,
            });
            continue;
        }

        return Ok(result);
    }
}
