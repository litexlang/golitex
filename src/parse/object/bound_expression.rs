//! Lower aggregate and limit expression binders to ordinary anonymous functions.

use super::{is_atom_name, parse_obj};
use crate::parse::keywords::{COMMA, LEFT_PAREN, RIGHT_PAREN};
use crate::prelude::*;
use crate::tokenize::TokenBlock;

#[cfg(test)]
#[path = "../../../tests/unit/parse/bound_expressions.rs"]
mod tests;

pub(super) fn parse_bound_expression(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
    name: &str,
) -> RuntimeResult<Option<Obj>> {
    let (outer_count, parameters) = match name {
        "sum_of" | "prod_of" => (2, "k, a, b, E"),
        "set_sum_of" | "set_prod_of" => (1, "k, S, E"),
        "lim_of" => (0, "n, E"),
        "fn_lim_of" => (2, "x, D, x0, E"),
        _ => return Ok(None),
    };
    tb.advance()?;
    tb.expect(LEFT_PAREN)?;
    let parameter_name = tb.advance()?;
    if !is_atom_name(&parameter_name) {
        return Err(tb.parse_error(format!(
            "`{name}` expects a bound variable first: `{name}({parameters})`"
        )));
    }
    let mut outer_args = Vec::with_capacity(outer_count);
    for _ in 0..outer_count {
        if tb.peek() != Some(COMMA) {
            return Err(tb.parse_error(format!("expected `{name}({parameters})`")));
        }
        tb.advance()?;
        outer_args.push(parse_obj(rt, tb)?);
    }
    if tb.peek() != Some(COMMA) || tb.peek_at(1) == Some(RIGHT_PAREN) {
        return Err(tb.parse_error(format!("expected `{name}({parameters})`")));
    }
    tb.advance()?;

    let domain = match name {
        "sum_of" | "prod_of" => Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
            start: Box::new(outer_args[0].clone()),
            end: Box::new(outer_args[1].clone()),
        })),
        "lim_of" => Obj::StandardSet(StandardSet::NPos),
        _ => outer_args[0].clone(),
    };

    rt.push_parse_scope();
    let parsed_body: RuntimeResult<_> = (|| {
        let parameter = rt.define_plain_atom_as_parse(tb, parameter_name)?;
        let expression = parse_obj(rt, tb)?;
        Ok((parameter, expression))
    })();
    rt.pop_parse_scope();
    let (parameter, expression) = parsed_body?;
    if tb.peek() != Some(RIGHT_PAREN) {
        return Err(tb.parse_error(format!("expected `{name}({parameters})`")));
    }
    tb.expect(RIGHT_PAREN)?;

    let function = Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
        body: FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![parameter],
                    param_type: Box::new(domain),
                }],
            },
            dom_facts: vec![],
            ret_set: Box::new(Obj::StandardSet(StandardSet::R)),
        },
        equal_to: Box::new(expression),
    }));

    let mut args = outer_args.into_iter();
    let result = match name {
        "sum_of" => Obj::IteratedOperator(IteratedOperator::Sum(Sum {
            start: Box::new(args.next().unwrap()),
            end: Box::new(args.next().unwrap()),
            func: Box::new(function),
        })),
        "prod_of" => Obj::IteratedOperator(IteratedOperator::Product(Product {
            start: Box::new(args.next().unwrap()),
            end: Box::new(args.next().unwrap()),
            func: Box::new(function),
        })),
        "set_sum_of" => Obj::IteratedOperator(IteratedOperator::SumOfFiniteSet(SumOfFiniteSet {
            set: Box::new(args.next().unwrap()),
            func: Box::new(function),
        })),
        "set_prod_of" => {
            Obj::IteratedOperator(IteratedOperator::ProductOfFiniteSet(ProductOfFiniteSet {
                set: Box::new(args.next().unwrap()),
                func: Box::new(function),
            }))
        }
        "lim_of" => SequenceLimit::new(function).into(),
        "fn_lim_of" => FunctionLimit::new(function, args.nth(1).unwrap()).into(),
        _ => unreachable!("only bound expression keywords reach this point"),
    };
    Ok(Some(result))
}
