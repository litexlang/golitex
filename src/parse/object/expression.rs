use super::primary::{fn_obj_head_from_obj, parse_primary};
use crate::ast::obj::{
    Add, ArithmeticOperator, Cart, ClosedRange, Div, Factorial, FieldAccess, FnObj, FnSet,
    FunctionSpace, IntegerOperator, Intersect, Mod, Mul, Neg, Obj, Pow, ProductShape, SetFormer,
    SetOperator, StructAndFieldAccessObj, Sub, Union,
};
use crate::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
use crate::parse::keywords::{
    ADD, BANG, DIV, DOT, DOT_DOT_DOT, FN_ARROW, LEFT_BRACKET, LEFT_PAREN, MOD_OP, MUL, POW, SUB,
    UNICODE_CART, UNICODE_INTERSECT, UNICODE_UNION,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::tokenize::TokenBlock;

pub fn parse_obj(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    parse_fn_arrow(rt, tb)
}

// `A -> B` desugars to `fn(__param_<id> A) B` (right-associative).
// Example: `R -> R -> Z` = `R -> (R -> Z)`.
fn parse_fn_arrow(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let left = parse_unicode_union(rt, tb)?;
    if tb.peek() != Some(FN_ARROW) {
        return Ok(left);
    }
    tb.advance()?;
    let right = parse_fn_arrow(rt, tb)?;
    let param = rt.fresh_internal_param();
    Ok(Obj::FunctionSpace(FunctionSpace::FnSet(FnSet {
        set_bound_parameters: SetBoundParameterList {
            groups: vec![SetBoundParameterGroup {
                params: vec![param],
                param_type: Box::new(left),
            }],
        },
        dom_facts: vec![],
        ret_set: Box::new(right),
    })))
}

fn parse_unicode_union(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_unicode_intersect(rt, tb)?;
    while tb.peek() == Some(UNICODE_UNION) {
        tb.advance()?;
        let right = parse_unicode_intersect(rt, tb)?;
        left = Obj::SetOperator(SetOperator::Union(Union {
            left: Box::new(left),
            right: Box::new(right),
        }));
    }
    Ok(left)
}

fn parse_unicode_intersect(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_unicode_cart(rt, tb)?;
    while tb.peek() == Some(UNICODE_INTERSECT) {
        tb.advance()?;
        let right = parse_unicode_cart(rt, tb)?;
        left = Obj::SetOperator(SetOperator::Intersect(Intersect {
            left: Box::new(left),
            right: Box::new(right),
        }));
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
    Ok(Obj::ProductShape(ProductShape::Cart(Cart {
        args: factors.into_iter().map(Box::new).collect(),
    })))
}

fn parse_add_sub(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_mul_div_mod(rt, tb)?;
    loop {
        match tb.peek() {
            Some(ADD) => {
                tb.advance()?;
                let right = parse_mul_div_mod(rt, tb)?;
                left = Obj::ArithmeticOperator(ArithmeticOperator::Add(Add {
                    left: Box::new(left),
                    right: Box::new(right),
                }));
            }
            Some(SUB) => {
                tb.advance()?;
                let right = parse_mul_div_mod(rt, tb)?;
                left = Obj::ArithmeticOperator(ArithmeticOperator::Sub(Sub {
                    left: Box::new(left),
                    right: Box::new(right),
                }));
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
                left = Obj::ArithmeticOperator(ArithmeticOperator::Mul(Mul {
                    left: Box::new(left),
                    right: Box::new(right),
                }));
            }
            Some(DIV) => {
                tb.advance()?;
                let right = parse_closed_range(rt, tb)?;
                left = Obj::ArithmeticOperator(ArithmeticOperator::Div(Div {
                    left: Box::new(left),
                    right: Box::new(right),
                }));
            }
            Some(MOD_OP) => {
                tb.advance()?;
                let right = parse_closed_range(rt, tb)?;
                left = Obj::IntegerOperator(IntegerOperator::Mod(Mod {
                    left: Box::new(left),
                    right: Box::new(right),
                }));
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
        Ok(Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
            start: Box::new(left),
            end: Box::new(right),
        })))
    } else {
        Ok(left)
    }
}

fn parse_unary(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    if tb.peek() == Some(SUB) {
        tb.advance()?;
        let arg = parse_unary(rt, tb)?;
        return Ok(Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg {
            arg: Box::new(arg),
        })));
    }
    parse_pow(rt, tb)
}

fn parse_pow(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let left = parse_postfix(rt, tb)?;
    if tb.peek() == Some(POW) {
        tb.advance()?;
        // Right-associative: a^b^c = a^(b^c); right side re-enters unary.
        let right = parse_unary(rt, tb)?;
        Ok(Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
            base: Box::new(left),
            exponent: Box::new(right),
        })))
    } else {
        Ok(left)
    }
}

fn parse_postfix(rt: &mut Runtime, tb: &mut TokenBlock) -> RuntimeResult<Obj> {
    let mut left = parse_primary(rt, tb)?;
    left = parse_field_and_call_postfixes(rt, tb, left)?;
    left = parse_optional_factorial_bang(tb, left)?;
    if tb.peek() == Some(LEFT_BRACKET) {
        return Err(tb.parse_error("object indexing with [] is removed: use ordinary function application t(i); singleton tuples use tuple(a)"));
    }
    Ok(left)
}

// Postfix `!` → Factorial. Tokenizer keeps `!=` as one token, so this does not
// steal inequality. `exist!` is parsed in fact keywords as `exist` then `!`.
// Example: `3!`, `n!`, `(n+1)!`, `f(n)!`.
fn parse_optional_factorial_bang(tb: &mut TokenBlock, left: Obj) -> RuntimeResult<Obj> {
    if tb.peek() != Some(BANG) {
        return Ok(left);
    }
    tb.advance()?;
    Ok(Obj::IntegerOperator(IntegerOperator::Factorial(
        Factorial {
            arg: Box::new(left),
        },
    )))
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
            result = match result {
                Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(mut access)) => {
                    access.fields.push(field_name);
                    Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(access))
                }
                other => Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(
                    FieldAccess {
                        obj: Box::new(other),
                        fields: vec![field_name],
                    },
                )),
            };
            continue;
        }

        if tb.peek() == Some(LEFT_PAREN) {
            let (head, mut body_vectors) = match result {
                Obj::FnObj(call) => (*call.head, call.body),
                other => (
                    fn_obj_head_from_obj(other)
                        .expect("all object expressions have an application head"),
                    Vec::new(),
                ),
            };
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
