//! Explicit chain-rule and integral-substitution laws; no integration search.
mod helper;
#[cfg(test)]
#[path = "../../../../tests/unit/execute/riemann_integral/substitution.rs"]
mod tests;

use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::antiderivative::{domain_requirements, relation};
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply as call;
use crate::execute::execute_fact_stmt::riemann_integral::helper::*;
use crate::prelude::*;
use helper::*;

pub(super) fn prepare(
    rt: &mut Runtime,
    theorem: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    if theorem == BuiltinTheoremId::AntiderivativeCompose {
        // F'=f, g'=dg => (F o g)' = (f o g)*dg on an open region.
        let region = args[6].clone();
        let target = args[7].clone();
        let mut req = Vec::new();
        for (primitive, function, domain) in [
            (&args[0], &args[1], &target),
            (&args[2], &args[3], &region),
            (&args[4], &args[5], &region),
        ] {
            let Some(requirements) = domain_requirements(
                rt,
                &[primitive.clone(), function.clone(), domain.clone()],
                VerifyState::new(VerifyStateLevel::BuiltinRule),
            )?
            else {
                return Ok(Err(
                    "requires unary real functions covering explicit open regions".into(),
                ));
            };
            req.extend(requirements);
        }
        req.push(relation(rt, args[0].clone(), args[1].clone(), target.clone()).into());
        req.push(image(rt, args[2].clone(), region.clone(), target));
        req.push(derivative(
            rt,
            args[2].clone(),
            args[3].clone(),
            region.clone(),
        ));
        let x = rt.fresh_internal_param();
        let gx = call(args[2].clone(), id(&x));
        let primitive = eq(
            rt,
            call(args[4].clone(), id(&x)),
            call(args[0].clone(), gx.clone()),
        );
        let integrand = eq(
            rt,
            call(args[5].clone(), id(&x)),
            mul(call(args[1].clone(), gx), call(args[3].clone(), id(&x))),
        );
        req.push(super::helper::forall(
            rt,
            x,
            region.clone(),
            vec![],
            vec![primitive, integrand],
        ));
        return Ok(Ok((
            req,
            vec![relation(rt, args[4].clone(), args[5].clone(), region).into()],
        )));
    }
    if theorem != BuiltinTheoremId::RiemannIntegralSubstitution {
        return Ok(Err("not a calculus substitution theorem".into()));
    }

    // Continuous f on J, C1 g on [a,b], g([a,b]) subset J, and
    // h=(f o g)*g' imply integral(h,a,b)=integral(f,g(a),g(b)).
    // No monotonicity is required. Endpoint images alone are insufficient.
    let (f, g, dg, h) = (&args[0], &args[1], &args[2], &args[3]);
    let target = args[4].clone();
    let (a, b) = (args[5].clone(), args[6].clone());
    let region = sorted_interval(a.clone(), b.clone());
    let Some(mut req) = interval_region(rt, &target) else {
        return Ok(Err(
            "outer continuity region must be R or an explicit real open/closed interval".into(),
        ));
    };
    req.push(member(rt, a.clone(), real()).into());
    req.push(member(rt, b.clone(), real()).into());
    for (function, domain) in [(f, &target), (g, &region), (dg, &region), (h, &region)] {
        let Some(requirements) = covering(rt, function, domain)? else {
            return Ok(Err(
                "requires complete unary real functions covering their respective regions".into(),
            ));
        };
        req.extend(requirements);
    }
    req.push(continuous(rt, f.clone(), target.clone()));
    req.push(continuous(rt, g.clone(), region.clone()));
    req.push(continuous(rt, dg.clone(), region.clone()));
    req.push(image(rt, g.clone(), region.clone(), target));
    req.push(derivative(rt, g.clone(), dg.clone(), region.clone()));
    let x = rt.fresh_internal_param();
    let product = eq(
        rt,
        call(h.clone(), id(&x)),
        mul(
            call(f.clone(), call(g.clone(), id(&x))),
            call(dg.clone(), id(&x)),
        ),
    );
    req.push(super::helper::forall(rt, x, region, vec![], vec![product]));
    req.push(
        rt.riemann_integral_candidate(
            f.clone(),
            call(g.clone(), a.clone()),
            call(g.clone(), b.clone()),
            args[7].clone(),
        )
        .into(),
    );
    let conclusion = rt.riemann_integral_candidate(h.clone(), a, b, args[7].clone());
    Ok(Ok((req, vec![conclusion.into()])))
}
