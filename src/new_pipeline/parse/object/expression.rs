use super::primary::{fn_obj_head_from_obj, parse_primary};
use crate::new_pipeline::ast::obj::{
    Add, Cart, ClosedRange, Div, FnObj, Intersect, Mod, Mul, Number, Obj,
    ObjAsStructInstanceWithFieldAccess, ObjAtIndex, Pow, Sub, Union,
};
use crate::new_pipeline::parse::keywords::{
    ADD, DIV, DOT, DOT_DOT_DOT, LEFT_BRACKET, LEFT_PAREN, MOD_OP, MUL, POW, RIGHT_BRACKET, SUB,
    UNICODE_CART, UNICODE_INTERSECT, UNICODE_UNION,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::tokenize::TokenBlock;

pub fn parse_obj(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    parse_unicode_union(rt, tb)
}

fn parse_unicode_union(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_unicode_intersect(rt, tb)?;
    while tb.peek() == Some(UNICODE_UNION) {
        tb.advance()?;
        let right = parse_unicode_intersect(rt, tb)?;
        left = Obj::Union(Union {
            left: Box::new(left),
            right: Box::new(right),
        });
    }
    Ok(left)
}

fn parse_unicode_intersect(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_unicode_cart(rt, tb)?;
    while tb.peek() == Some(UNICODE_INTERSECT) {
        tb.advance()?;
        let right = parse_unicode_cart(rt, tb)?;
        left = Obj::Intersect(Intersect {
            left: Box::new(left),
            right: Box::new(right),
        });
    }
    Ok(left)
}

fn parse_unicode_cart(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let first = parse_add_sub(rt, tb)?;
    if tb.peek() != Some(UNICODE_CART) {
        return Ok(first);
    }
    let mut factors = vec![first];
    while tb.peek() == Some(UNICODE_CART) {
        tb.advance()?;
        factors.push(parse_add_sub(rt, tb)?);
    }
    Ok(Obj::Cart(Cart {
        args: factors.into_iter().map(Box::new).collect(),
    }))
}

fn parse_add_sub(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_mul_div_mod(rt, tb)?;
    loop {
        match tb.peek() {
            Some(ADD) => {
                tb.advance()?;
                let right = parse_mul_div_mod(rt, tb)?;
                left = Obj::Add(Add {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            Some(SUB) => {
                tb.advance()?;
                let right = parse_mul_div_mod(rt, tb)?;
                left = Obj::Sub(Sub {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            _ => return Ok(left),
        }
    }
}

fn parse_mul_div_mod(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_closed_range(rt, tb)?;
    loop {
        match tb.peek() {
            Some(MUL) => {
                tb.advance()?;
                let right = parse_closed_range(rt, tb)?;
                left = Obj::Mul(Mul {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            Some(DIV) => {
                tb.advance()?;
                let right = parse_closed_range(rt, tb)?;
                left = Obj::Div(Div {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            Some(MOD_OP) => {
                tb.advance()?;
                let right = parse_closed_range(rt, tb)?;
                left = Obj::Mod(Mod {
                    left: Box::new(left),
                    right: Box::new(right),
                });
            }
            _ => return Ok(left),
        }
    }
}

fn parse_closed_range(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let left = parse_unary(rt, tb)?;
    if tb.peek() == Some(DOT_DOT_DOT) {
        tb.advance()?;
        let right = parse_add_sub(rt, tb)?;
        Ok(Obj::ClosedRange(ClosedRange {
            start: Box::new(left),
            end: Box::new(right),
        }))
    } else {
        Ok(left)
    }
}

fn parse_unary(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    if tb.peek() == Some(SUB) {
        tb.advance()?;
        let right = parse_unary(rt, tb)?;
        // Encode unary minus as `0 - right` (no Neg variant).
        return Ok(Obj::Sub(Sub {
            left: Box::new(Obj::Number(Number {
                normalized_value: "0".to_string(),
            })),
            right: Box::new(right),
        }));
    }
    parse_pow(rt, tb)
}

fn parse_pow(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let left = parse_postfix(rt, tb)?;
    if tb.peek() == Some(POW) {
        tb.advance()?;
        // Right-associative: a^b^c = a^(b^c); right side re-enters unary.
        let right = parse_unary(rt, tb)?;
        Ok(Obj::Pow(Pow {
            base: Box::new(left),
            exponent: Box::new(right),
        }))
    } else {
        Ok(left)
    }
}

fn parse_postfix(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_primary(rt, tb)?;
    left = parse_field_and_call_postfixes(rt, tb, left)?;
    loop {
        if tb.peek() != Some(LEFT_BRACKET) {
            break;
        }
        tb.advance()?;
        let index = parse_obj(rt, tb)?;
        tb.expect(RIGHT_BRACKET)?;
        left = Obj::ObjAtIndex(ObjAtIndex {
            obj: Box::new(left),
            index: Box::new(index),
        });
        left = parse_field_and_call_postfixes(rt, tb, left)?;
    }
    Ok(left)
}

fn parse_field_and_call_postfixes(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
    mut result: Obj,
) -> RuntimeResult<Obj> {
    loop {
        if tb.peek() == Some(DOT) {
            tb.advance()?;
            let field_name = tb.advance()?;
            if !super::primary::is_simple_name(&field_name) {
                return Err(
                    tb.parse_error(format!("expected field name after `.`, got `{field_name}`"))
                );
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
                let args = super::primary::parse_obj_list_paren(rt, tb)?;
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
