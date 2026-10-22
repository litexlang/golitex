//! Explicit relation laws; constant difference uses the mean-value theorem.
use super::helper::{forall, identifier};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::antiderivative::{
    definition, domain_requirements, relation,
};
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply as call;
use crate::execute::execute_fact_stmt::riemann_integral::helper::*;
use crate::prelude::*;

pub(super) fn prepare(
    rt: &mut Runtime,
    theorem: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let (f, g, region) = (args[0].clone(), args[1].clone(), args[2].clone());
    if theorem == AntiderivativeDifferenceConstant {
        // F and G have the same derivative on a nonempty open interval.
        let interval = open_interval(args[3].clone(), args[4].clone());
        let mut req = vec![
            lt(rt, args[3].clone(), args[4].clone()).into(),
            member(rt, args[5].clone(), interval.clone()).into(),
        ];
        for primitive in [&f, &g] {
            let Some(requirements) = domain_requirements(
                rt,
                &[primitive.clone(), args[2].clone(), interval.clone()],
                VerifyState::new(VerifyStateLevel::BuiltinRule),
            )?
            else {
                return Ok(Err(
                    "requires complete unary real functions covering the open interval".into(),
                ));
            };
            req.extend(requirements);
        }
        req.push(relation(rt, f.clone(), args[2].clone(), interval.clone()).into());
        req.push(relation(rt, g.clone(), args[2].clone(), interval.clone()).into());
        let x = rt.fresh_internal_param();
        let at_x = sub(
            call(f.clone(), identifier(&x)),
            call(g.clone(), identifier(&x)),
        );
        let constant = sub(call(f, args[5].clone()), call(g, args[5].clone()));
        let equation = eq(rt, at_x, constant);
        return Ok(Ok((
            req,
            vec![forall(rt, x, interval, vec![], vec![equation])],
        )));
    }
    let region_index = match theorem {
        AntiderivativeShift => 3,
        AntiderivativeAdd => 6,
        AntiderivativeScale => 4,
        _ => 2,
    };
    let region = if region_index == 2 {
        region
    } else {
        args[region_index].clone()
    };
    let Some(mut req) = domain_requirements(
        rt,
        &[f.clone(), g.clone(), region.clone()],
        VerifyState::new(VerifyStateLevel::BuiltinRule),
    )?
    else {
        return Ok(Err(
            "requires complete unary real functions covering the region".into(),
        ));
    };
    let result = match theorem {
        AntiderivativeFromDefinition => {
            req.push(definition(rt, f.clone(), g.clone(), region.clone()));
            vec![relation(rt, f, g, region).into()]
        }
        AntiderivativeToDefinition => {
            req.push(relation(rt, f.clone(), g.clone(), region.clone()).into());
            vec![definition(rt, f, g, region)]
        }
        AntiderivativeRestrict => {
            req.push(relation(rt, f.clone(), g.clone(), region.clone()).into());
            req.push(subset(rt, args[3].clone(), region).into());
            vec![relation(rt, f, g, args[3].clone()).into()]
        }
        AntiderivativeShift => {
            req.push(relation(rt, f.clone(), g.clone(), region.clone()).into());
            req.push(member(rt, args[4].clone(), real()).into());
            let x = rt.fresh_internal_param();
            let equation = eq(
                rt,
                call(args[2].clone(), identifier(&x)),
                add(call(f, identifier(&x)), args[4].clone()),
            );
            req.push(forall(rt, x, region.clone(), vec![], vec![equation]));
            vec![relation(rt, args[2].clone(), g, region).into()]
        }
        AntiderivativeAdd | AntiderivativeScale => {
            req.push(relation(rt, f.clone(), g.clone(), region.clone()).into());
            let (primitive, function, body, value) = if theorem == AntiderivativeAdd {
                req.push(relation(rt, args[2].clone(), args[3].clone(), region.clone()).into());
                (
                    args[4].clone(),
                    args[5].clone(),
                    args[2].clone(),
                    args[3].clone(),
                )
            } else {
                req.push(member(rt, args[5].clone(), real()).into());
                (
                    args[2].clone(),
                    args[3].clone(),
                    args[5].clone(),
                    args[5].clone(),
                )
            };
            let x = rt.fresh_internal_param();
            let xx = identifier(&x);
            let (primitive_body, function_body) = if theorem == AntiderivativeAdd {
                (
                    add(call(f, xx.clone()), call(body, xx.clone())),
                    add(call(g, xx.clone()), call(value, xx.clone())),
                )
            } else {
                (
                    mul(body, call(f, xx.clone())),
                    mul(value, call(g, xx.clone())),
                )
            };
            let primitive_eq = eq(rt, call(primitive.clone(), xx.clone()), primitive_body);
            let function_eq = eq(rt, call(function.clone(), xx), function_body);
            req.push(forall(
                rt,
                x,
                region.clone(),
                vec![],
                vec![primitive_eq, function_eq],
            ));
            vec![relation(rt, primitive, function, region).into()]
        }
        _ => return Ok(Err("not an antiderivative theorem".into())),
    };
    Ok(Ok((req, result)))
}
