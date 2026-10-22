//! Explicit Riemann integral laws. Every premise is checked before storage.
use super::helper::{forall, identifier};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply as call;
use crate::execute::execute_fact_stmt::riemann_integral::helper::*;
use crate::prelude::*;

pub(super) fn prepare(
    rt: &mut Runtime,
    theorem: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let (ai, bi) = match theorem {
        RiemannIntegralByParts => (6, 7),
        RiemannIntegralAdd | RiemannIntegralSubtract => (3, 4),
        RiemannIntegralScale
        | RiemannIntegralExtensional
        | RiemannIntegralCompare
        | RiemannIntegralNewtonLeibniz => (2, 3),
        RiemannIntegralSplit | RiemannIntegralStep => (1, 3),
        RiemannIntegralZero => (1, 1),
        _ => (1, 2),
    };
    let f = args[0].clone();
    let a = args[ai].clone();
    let b = args[bi].clone();
    let Some(mut req) = context(rt, &f, &a, &b)? else {
        return Ok(Err(
            "requires a complete unary real function covering the sorted closed interval".into(),
        ));
    };
    let result = match theorem {
        RiemannIntegralByParts => {
            // C1 version of integral(u*v') = [u*v] - integral(u'*v).
            // Explicit derivative functions and product functions preserve all
            // endpoint domains; a known right-hand candidate supplies its value.
            let region = sorted_interval(a.clone(), b.clone());
            for function in &args[1..6] {
                let Some(requirements) = context(rt, function, &a, &b)? else {
                    return Ok(Err(
                        "every function must cover the sorted closed interval".into()
                    ));
                };
                req.extend(requirements);
            }
            for function in &args[..4] {
                req.push(continuity(rt, function.clone(), region.clone()));
            }
            let x = rt.fresh_internal_param();
            let xx = identifier(&x);
            let du =
                rt.derivative_candidate(f.clone(), xx.clone(), call(args[1].clone(), xx.clone()));
            let dv = rt.derivative_candidate(
                args[2].clone(),
                xx.clone(),
                call(args[3].clone(), xx.clone()),
            );
            let left = eq(
                rt,
                call(args[4].clone(), xx.clone()),
                mul(
                    call(f.clone(), xx.clone()),
                    call(args[3].clone(), xx.clone()),
                ),
            );
            let right = eq(
                rt,
                call(args[5].clone(), xx.clone()),
                mul(call(args[1].clone(), xx.clone()), call(args[2].clone(), xx)),
            );
            req.push(forall(rt, x, region, vec![], vec![du, dv, left, right]));
            req.push(
                rt.riemann_integral_candidate(
                    args[5].clone(),
                    a.clone(),
                    b.clone(),
                    args[8].clone(),
                )
                .into(),
            );
            let boundary = sub(
                mul(call(f.clone(), b.clone()), call(args[2].clone(), b.clone())),
                mul(call(f, a.clone()), call(args[2].clone(), a.clone())),
            );
            let value = sub(boundary, args[8].clone());
            vec![rt
                .riemann_integral_candidate(args[4].clone(), a, b, value)
                .into()]
        }
        RiemannIntegralFromDefinition | RiemannIntegralToDefinition => {
            let candidate = rt.riemann_integral_candidate(f, a, b, args[3].clone());
            req.push(member(rt, args[3].clone(), real()).into());
            let clauses = rt
                .riemann_integral_defining_clauses(
                    &candidate,
                    VerifyState::new(VerifyStateLevel::BuiltinRule),
                )?
                .expect("candidate definition");
            if theorem == RiemannIntegralFromDefinition {
                req.extend(clauses);
                vec![candidate.into()]
            } else {
                req.push(candidate.into());
                clauses
            }
        }
        RiemannIntegralExists | RiemannIntegrableFromCandidate => {
            req.push(
                rt.riemann_integral_candidate(f.clone(), a.clone(), b.clone(), args[3].clone())
                    .into(),
            );
            if theorem == RiemannIntegralExists {
                vec![rt.riemann_integral_existence(f, a, b)]
            } else {
                vec![rt.riemann_integrable(f, a, b).into()]
            }
        }
        RiemannIntegralSelected => {
            req.push(rt.riemann_integral_existence(f.clone(), a.clone(), b.clone()));
            let value: RiemannIntegral = RiemannIntegral::new(f.clone(), a.clone(), b.clone());
            vec![rt.riemann_integral_candidate(f, a, b, value.into()).into()]
        }
        RiemannIntegralUnique => {
            req.push(
                rt.riemann_integral_candidate(f.clone(), a.clone(), b.clone(), args[3].clone())
                    .into(),
            );
            req.push(
                rt.riemann_integral_candidate(f, a, b, args[4].clone())
                    .into(),
            );
            vec![eq(rt, args[3].clone(), args[4].clone()).into()]
        }
        RiemannIntegralZero => vec![rt.riemann_integral_candidate(f, a, b, num("0")).into()],
        RiemannIntegralConstant | RiemannIntegralPower => {
            let x = rt.fresh_internal_param();
            let x_obj = identifier(&x);
            let (body, value) = if theorem == RiemannIntegralConstant {
                req.push(member(rt, args[3].clone(), real()).into());
                (
                    args[3].clone(),
                    mul(args[3].clone(), sub(b.clone(), a.clone())),
                )
            } else {
                req.push(member(rt, args[3].clone(), Obj::StandardSet(StandardSet::N)).into());
                let exponent = add(args[3].clone(), num("1"));
                (
                    power(x_obj.clone(), args[3].clone()),
                    divide(
                        sub(
                            power(b.clone(), exponent.clone()),
                            power(a.clone(), exponent.clone()),
                        ),
                        exponent,
                    ),
                )
            };
            let equation = eq(rt, call(f.clone(), x_obj), body);
            req.push(forall(
                rt,
                x,
                sorted_interval(a.clone(), b.clone()),
                vec![],
                vec![equation],
            ));
            vec![rt.riemann_integral_candidate(f, a, b, value).into()]
        }
        RiemannIntegralReverse => {
            req.push(
                rt.riemann_integral_candidate(f.clone(), a.clone(), b.clone(), args[3].clone())
                    .into(),
            );
            vec![rt
                .riemann_integral_candidate(f, b, a, mul(num("-1"), args[3].clone()))
                .into()]
        }
        RiemannIntegralAdd | RiemannIntegralSubtract => {
            let g = args[1].clone();
            let h = args[2].clone();
            let Some(g_req) = context(rt, &g, &a, &b)? else {
                return Ok(Err("second function must cover the interval".into()));
            };
            let Some(h_req) = context(rt, &h, &a, &b)? else {
                return Ok(Err("result function must cover the interval".into()));
            };
            req.extend(g_req);
            req.extend(h_req);
            req.push(
                rt.riemann_integral_candidate(f.clone(), a.clone(), b.clone(), args[5].clone())
                    .into(),
            );
            req.push(
                rt.riemann_integral_candidate(g.clone(), a.clone(), b.clone(), args[6].clone())
                    .into(),
            );
            let x = rt.fresh_internal_param();
            let xx = identifier(&x);
            let (body, value) = if theorem == RiemannIntegralAdd {
                (
                    add(call(f, xx.clone()), call(g, xx.clone())),
                    add(args[5].clone(), args[6].clone()),
                )
            } else {
                (
                    sub(call(f, xx.clone()), call(g, xx.clone())),
                    sub(args[5].clone(), args[6].clone()),
                )
            };
            let equation = eq(rt, call(h.clone(), xx), body);
            req.push(forall(
                rt,
                x,
                sorted_interval(a.clone(), b.clone()),
                vec![],
                vec![equation],
            ));
            vec![rt.riemann_integral_candidate(h, a, b, value).into()]
        }
        RiemannIntegralScale => {
            let h = args[1].clone();
            let Some(h_req) = context(rt, &h, &a, &b)? else {
                return Ok(Err("scaled function must cover the interval".into()));
            };
            req.extend(h_req);
            req.push(member(rt, args[4].clone(), real()).into());
            req.push(
                rt.riemann_integral_candidate(f.clone(), a.clone(), b.clone(), args[5].clone())
                    .into(),
            );
            let x = rt.fresh_internal_param();
            let xx = identifier(&x);
            let equation = eq(
                rt,
                call(h.clone(), xx.clone()),
                mul(args[4].clone(), call(f, xx)),
            );
            req.push(forall(
                rt,
                x,
                sorted_interval(a.clone(), b.clone()),
                vec![],
                vec![equation],
            ));
            vec![rt
                .riemann_integral_candidate(h, a, b, mul(args[4].clone(), args[5].clone()))
                .into()]
        }
        RiemannIntegralSplit => {
            let c = args[2].clone();
            req.push(member(rt, c.clone(), sorted_interval(a.clone(), b.clone())).into());
            req.push(
                rt.riemann_integral_candidate(f.clone(), a.clone(), c.clone(), args[4].clone())
                    .into(),
            );
            req.push(
                rt.riemann_integral_candidate(f.clone(), c, b.clone(), args[5].clone())
                    .into(),
            );
            vec![rt
                .riemann_integral_candidate(f, a, b, add(args[4].clone(), args[5].clone()))
                .into()]
        }
        RiemannIntegralExtensional => {
            let g = args[1].clone();
            let Some(g_req) = context(rt, &g, &a, &b)? else {
                return Ok(Err("second function must cover the interval".into()));
            };
            req.extend(g_req);
            req.push(
                rt.riemann_integral_candidate(f.clone(), a.clone(), b.clone(), args[4].clone())
                    .into(),
            );
            let x = rt.fresh_internal_param();
            let xx = identifier(&x);
            let equation = eq(rt, call(f, xx.clone()), call(g.clone(), xx));
            req.push(forall(
                rt,
                x,
                sorted_interval(a.clone(), b.clone()),
                vec![],
                vec![equation],
            ));
            vec![rt
                .riemann_integral_candidate(g, a, b, args[4].clone())
                .into()]
        }
        RiemannIntegralCompare => {
            let g = args[1].clone();
            let Some(g_req) = context(rt, &g, &a, &b)? else {
                return Ok(Err("second function must cover the interval".into()));
            };
            req.extend(g_req);
            req.push(le(rt, a.clone(), b.clone()).into());
            req.push(
                rt.riemann_integral_candidate(f.clone(), a.clone(), b.clone(), args[4].clone())
                    .into(),
            );
            req.push(
                rt.riemann_integral_candidate(g.clone(), a.clone(), b.clone(), args[5].clone())
                    .into(),
            );
            let x = rt.fresh_internal_param();
            let xx = identifier(&x);
            let comparison = le(rt, call(f, xx.clone()), call(g, xx));
            req.push(forall(rt, x, interval(a, b), vec![], vec![comparison]));
            vec![le(rt, args[4].clone(), args[5].clone()).into()]
        }
        RiemannIntegralBound => {
            req.push(
                rt.riemann_integral_candidate(f.clone(), a.clone(), b.clone(), args[3].clone())
                    .into(),
            );
            req.push(member(rt, args[4].clone(), real()).into());
            req.push(le(rt, num("0"), args[4].clone()).into());
            let x = rt.fresh_internal_param();
            let bound = le(rt, abs(call(f, identifier(&x))), args[4].clone());
            req.push(forall(
                rt,
                x,
                sorted_interval(a.clone(), b.clone()),
                vec![],
                vec![bound],
            ));
            vec![le(
                rt,
                abs(args[3].clone()),
                mul(args[4].clone(), abs(sub(b, a))),
            )
            .into()]
        }
        RiemannIntegrableContinuous => {
            req.push(continuity(
                rt,
                f.clone(),
                sorted_interval(a.clone(), b.clone()),
            ));
            vec![rt.riemann_integrable(f, a, b).into()]
        }
        RiemannIntegralNewtonLeibniz => {
            let primitive = args[1].clone();
            let Some(f_req) = context(rt, &primitive, &a, &b)? else {
                return Ok(Err("primitive must cover the closed interval".into()));
            };
            req.extend(f_req);
            req.push(
                rt.riemann_integrable(f.clone(), a.clone(), b.clone())
                    .into(),
            );
            req.push(continuity(
                rt,
                primitive.clone(),
                sorted_interval(a.clone(), b.clone()),
            ));
            let x = rt.fresh_internal_param();
            let derivative =
                rt.derivative_candidate(primitive.clone(), identifier(&x), call(f, identifier(&x)));
            req.push(forall(
                rt,
                x,
                open_interval(min(a.clone(), b.clone()), max(a.clone(), b.clone())),
                vec![],
                vec![derivative],
            ));
            let value = sub(
                call(primitive.clone(), b.clone()),
                call(primitive, a.clone()),
            );
            vec![rt
                .riemann_integral_candidate(args[0].clone(), a, b, value)
                .into()]
        }
        RiemannIntegralStep => {
            let c = args[2].clone();
            req.push(member(rt, c.clone(), interval(a.clone(), b.clone())).into());
            req.push(member(rt, args[4].clone(), real()).into());
            req.push(member(rt, args[5].clone(), real()).into());
            let left_interval = Obj::SetFormer(SetFormer::IntervalObj(
                IntervalObj::LeftClosedRightOpen(IntervalObjStruct {
                    start: Box::new(a.clone()),
                    end: Box::new(c.clone()),
                }),
            ));
            let right_interval = Obj::SetFormer(SetFormer::IntervalObj(
                IntervalObj::LeftOpenRightClosed(IntervalObjStruct {
                    start: Box::new(c.clone()),
                    end: Box::new(b.clone()),
                }),
            ));
            for (domain, value) in [
                (left_interval, args[4].clone()),
                (right_interval, args[5].clone()),
            ] {
                let x = rt.fresh_internal_param();
                let equation = eq(rt, call(f.clone(), identifier(&x)), value);
                req.push(forall(rt, x, domain, vec![], vec![equation]));
            }
            let value = add(
                mul(args[4].clone(), sub(c.clone(), a.clone())),
                mul(args[5].clone(), sub(b.clone(), c)),
            );
            vec![rt.riemann_integral_candidate(f, a, b, value).into()]
        }
        DarbouxEnclosureFromDefinition | DarbouxEnclosureToDefinition => {
            let clauses = enclosure_clauses(rt, args);
            let certificate = certificate(rt, "is_darboux_enclosure", args.to_vec());
            if theorem == DarbouxEnclosureFromDefinition {
                req.extend(clauses);
                vec![certificate.into()]
            } else {
                req.push(certificate.into());
                clauses
            }
        }
        _ => return Ok(Err("not a Riemann integral theorem".into())),
    };
    Ok(Ok((req, result)))
}
fn context(rt: &mut Runtime, f: &Obj, a: &Obj, b: &Obj) -> RuntimeResult<Option<Vec<Fact>>> {
    let Some(domain) =
        rt.checked_real_function_limit_domain(f, VerifyState::new(VerifyStateLevel::BuiltinRule))?
    else {
        return Ok(None);
    };
    Ok(Some(rt.riemann_domain_requirements(
        a.clone(),
        b.clone(),
        domain.domain,
    )))
}
fn continuity(rt: &mut Runtime, f: Obj, domain: Obj) -> Fact {
    let x = rt.fresh_internal_param();
    let condition = FunctionContinuousAtFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        function: f,
        point: identifier(&x),
        side: RealApproachSide::Both,
        line_file: None,
    }
    .into();
    forall(rt, x, domain, vec![], vec![condition])
}
fn power(base: Obj, exponent: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(base),
        exponent: Box::new(exponent),
    }))
}
fn divide(left: Obj, right: Obj) -> Obj {
    crate::rational_expression::helper::div_objs(left, right)
}
fn enclosure_clauses(rt: &mut Runtime, args: &[Obj]) -> Vec<Fact> {
    use crate::ast::param::*;
    let f = args[0].clone();
    let a = args[1].clone();
    let b = args[2].clone();
    let n = args[3].clone();
    let p = args[4].clone();
    let l = args[5].clone();
    let u = args[6].clone();
    let mut clauses = vec![
        lt(rt, a.clone(), b.clone()).into(),
        member(rt, n.clone(), Obj::StandardSet(StandardSet::NPos)).into(),
    ];
    for (value, domain) in [
        (p.clone(), integer_interval(num("0"), n.clone())),
        (l.clone(), integer_interval(num("1"), n.clone())),
        (u.clone(), integer_interval(num("1"), n.clone())),
    ] {
        let Obj::SetFormer(SetFormer::ClosedRange(range)) = domain else {
            unreachable!("integer index range")
        };
        let space = function_space(rt, *range.start, *range.end);
        clauses.push(member(rt, value, space).into());
    }
    clauses.push(eq(rt, call(p.clone(), num("0")), a.clone()).into());
    clauses.push(eq(rt, call(p.clone(), n.clone()), b.clone()).into());
    let i = rt.fresh_internal_param();
    let ii = identifier(&i);
    let left = call(p.clone(), sub(ii.clone(), num("1")));
    let right = call(p.clone(), ii.clone());
    let order = lt(rt, left.clone(), right.clone());
    let first = le(rt, a.clone(), left.clone());
    let last = le(rt, right.clone(), b.clone());
    clauses.push(forall(
        rt,
        i.clone(),
        integer_interval(num("1"), n.clone()),
        vec![],
        vec![order, first, last],
    ));
    let x = rt.fresh_internal_param();
    let xx = identifier(&x);
    let start = le(rt, left, xx.clone());
    let end = le(rt, xx.clone(), right);
    let lower = le(rt, call(l, ii.clone()), call(f.clone(), xx.clone()));
    let upper = le(rt, call(f, xx), call(u, ii));
    clauses.push(Fact::ForallFact(ForallFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList {
            groups: vec![
                typed(i, integer_interval(num("1"), n)),
                typed(x, interval(a, b)),
            ],
        },
        dom_facts: vec![start.into(), end.into()],
        then_facts: vec![
            ExistOrAndChainAtomicFact::AtomicFact(lower),
            ExistOrAndChainAtomicFact::AtomicFact(upper),
        ],
        line_file: None,
    }));
    clauses
}
