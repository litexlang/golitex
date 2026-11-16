//! Integral expression binders share ordinary function scope and real domains.
#[cfg(test)]
#[path = "../../../tests/unit/parse/integral_expressions.rs"]
mod tests;
use super::expression::parse_obj;
use super::primary::{is_atom_name, parse_obj_list_paren};
use crate::parse::keywords::{COMMA, LEFT_PAREN, RIGHT_PAREN};
use crate::prelude::*;
use crate::tokenize::TokenBlock;

pub(super) fn parse_integral(
    rt: &mut Runtime,
    tb: &mut TokenBlock,
    name: &str,
) -> RuntimeResult<Option<Obj>> {
    let (canonical, expression) = match name {
        "integ" => ("integral", true),
        "integ_oc" => ("integral_open_closed", true),
        "integ_co" => ("integral_closed_open", true),
        "integ_oo" => ("integral_open", true),
        "integ_pos_inf" => ("integral_pos_inf", true),
        "integ_neg_inf" => ("integral_neg_inf", true),
        "integral_open_closed"
        | "integral_closed_open"
        | "integral_open"
        | "integral_pos_inf"
        | "integral_neg_inf" => (name, false),
        _ => return Ok(None),
    };
    tb.advance()?;
    let endpoint_count = if matches!(canonical, "integral_pos_inf" | "integral_neg_inf") {
        1
    } else {
        2
    };
    let (function, endpoints) = if expression {
        tb.expect(LEFT_PAREN)?;
        let parameter_name = tb.advance()?;
        if !is_atom_name(&parameter_name) {
            return Err(tb.parse_error("integral expression expects a bound variable first"));
        }
        tb.expect(COMMA)?;
        let mut endpoints = Vec::new();
        for _ in 0..endpoint_count {
            endpoints.push(parse_obj(rt, tb)?);
            if tb.peek() != Some(COMMA) {
                return Err(tb.parse_error(format!("`{name}` expects a variable, {endpoint_count} endpoint(s), and an expression; use `{canonical}` for a function argument")));
            }
            tb.expect(COMMA)?;
        }
        let domain = integral_expression_domain(canonical, &endpoints);
        rt.push_parse_scope();
        let result: RuntimeResult<Obj> = (|| {
            if crate::builtin_theorem::is_reserved_builtin_name(&parameter_name)
                || crate::parse::keywords::is_reserved_object_name(&parameter_name)
            {
                return Err(
                    tb.parse_error(format!("`{parameter_name}` is a reserved builtin name"))
                );
            }
            let parameter = BoundName::new(rt.global_ids.allocate_identifier_id(), parameter_name);
            rt.parse_scope_stack
                .last_mut()
                .expect("integral binder scope")
                .plain
                .insert(parameter.name.clone(), parameter.id);
            let value = parse_obj(rt, tb)?;
            tb.expect(RIGHT_PAREN)?;
            Ok(Obj::FunctionSpace(FunctionSpace::AnonymousFn(
                AnonymousFn {
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
                    equal_to: Box::new(value),
                },
            )))
        })();
        rt.pop_parse_scope();
        (result?, endpoints)
    } else {
        let args = parse_obj_list_paren(rt, tb)?;
        if args.len() != endpoint_count + 1 {
            return Err(tb.parse_error(format!(
                "`{canonical}` expects a function and {endpoint_count} endpoint(s)"
            )));
        }
        (args[0].clone(), args[1..].to_vec())
    };
    if canonical == "integral" {
        return Ok(Some(
            RiemannIntegral::new(function, endpoints[0].clone(), endpoints[1].clone()).into(),
        ));
    }
    let bounds = ImproperIntegralBounds::from_name(canonical, &endpoints)
        .expect("checked integral name and arity");
    Ok(Some(ImproperIntegral::new(function, bounds).into()))
}

fn integral_expression_domain(name: &str, endpoints: &[Obj]) -> Obj {
    if name == "integral" {
        return crate::execute::execute_fact_stmt::riemann_integral::helper::sorted_interval(
            endpoints[0].clone(),
            endpoints[1].clone(),
        );
    }
    let bounds = ImproperIntegralBounds::from_name(name, endpoints).expect("checked integral name");
    crate::execute::execute_fact_stmt::improper_integral::integral_region(&bounds)
}
