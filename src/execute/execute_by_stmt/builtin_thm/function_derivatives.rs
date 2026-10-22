//! Explicit first-derivative laws on checked actual unary real domains.
use super::helper::*;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::pointwise_elementary::ElementaryRealFunction;
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply as call;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};
pub(super) fn prepare(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let real = Obj::StandardSet(StandardSet::R);
    if matches!(
        id,
        FnDerivativeAtRealInterior
            | FnDerivativeAtNonzeroInterior
            | FnDerivativeAtPositiveInterior
            | FnDerivativeAtNegativeInterior
    ) {
        let domain = Obj::StandardSet(match id {
            FnDerivativeAtRealInterior => StandardSet::R,
            FnDerivativeAtNonzeroInterior => StandardSet::RStar,
            FnDerivativeAtPositiveInterior => StandardSet::RPos,
            _ => StandardSet::RNeg,
        });
        let requirement = atomic_in(rt, args[0].clone(), domain.clone()).into();
        let interior = rt.derivative_interior_condition(domain, args[0].clone());
        return Ok(Ok((vec![requirement], vec![interior])));
    }
    let f = args[0].clone();
    let Some((mut req, df)) = super::continuity::context(rt, &f)? else {
        return Ok(Err("requires a complete unary real function".into()));
    };
    let binary = matches!(
        id,
        FnDerivativeAtAdd
            | FnDerivativeAtSubtract
            | FnDerivativeAtMultiply
            | FnDerivativeAtDivide
            | FnDerivativeAtCompose
    );
    let unary = matches!(
        id,
        FnDerivativeAtNeg | FnDerivativeAtScale | FnDerivativeAtPower
    );
    let point = args[if binary {
        3
    } else if unary {
        2
    } else {
        1
    }]
    .clone();
    req.push(atomic_in(rt, point.clone(), df.clone()).into());
    let elementary = match id {
        FnDerivativeAtExp => Some(ElementaryRealFunction::Exp),
        FnDerivativeAtLn => Some(ElementaryRealFunction::Ln),
        FnDerivativeAtSin => Some(ElementaryRealFunction::Sin),
        FnDerivativeAtCos => Some(ElementaryRealFunction::Cos),
        FnDerivativeAtSqrt => Some(ElementaryRealFunction::Sqrt),
        _ => None,
    };
    if let Some(kind) = elementary {
        req.push(rt.derivative_interior_condition(df.clone(), point.clone()));
        req.push(rt.elementary_real_condition(kind, point.clone(), true));
        let x = rt.fresh_internal_param();
        let equation = equal(
            rt,
            call(f.clone(), identifier(&x)),
            kind.apply(identifier(&x)),
        );
        req.push(forall(rt, x, df, vec![], vec![equation]));
        let result = rt.derivative_candidate(f, point.clone(), kind.derivative_factor(point));
        return Ok(Ok((req, vec![result.into()])));
    }
    let result = match id {
        FnDerivativeAtFromLimit => {
            req.push(atomic_in(rt, args[2].clone(), real).into());
            let candidate = rt.derivative_candidate(f.clone(), point, args[2].clone());
            req.extend(
                rt.derivative_defining_clauses(
                    &candidate,
                    VerifyState::new(VerifyStateLevel::BuiltinRule),
                )?
                .expect("derivative definition"),
            );
            vec![candidate.into()]
        }
        FnDerivativeAtToLimit => {
            req.push(
                rt.derivative_candidate(f.clone(), point.clone(), args[2].clone())
                    .into(),
            );
            let q = rt.derivative_difference_quotient(f, point.clone(), df);
            vec![rt
                .function_limit_candidate(
                    q,
                    LimitApproach::AtPoint(Box::new(point)),
                    args[2].clone(),
                )
                .into()]
        }
        FnDerivativeAtExists | FnDifferentiableAtFromDerivative | FnDerivativeAtContinuous => {
            req.push(
                rt.derivative_candidate(f.clone(), point.clone(), args[2].clone())
                    .into(),
            );
            vec![match id {
                FnDerivativeAtExists => rt.derivative_existence(f, point),
                FnDifferentiableAtFromDerivative => FunctionDifferentiableAtFact {
                    fact_id: rt.global_ids.allocate_fact_id(),
                    function: f,
                    point,
                    line_file: None,
                }
                .into(),
                _ => FunctionContinuousAtFact {
                    fact_id: rt.global_ids.allocate_fact_id(),
                    function: f,
                    point,
                    side: RealApproachSide::Both,
                    line_file: None,
                }
                .into(),
            }]
        }
        FnDifferentiableAtContinuous => {
            req.push(
                FunctionDifferentiableAtFact {
                    fact_id: rt.global_ids.allocate_fact_id(),
                    function: f.clone(),
                    point: point.clone(),
                    line_file: None,
                }
                .into(),
            );
            vec![FunctionContinuousAtFact {
                fact_id: rt.global_ids.allocate_fact_id(),
                function: f,
                point,
                side: RealApproachSide::Both,
                line_file: None,
            }
            .into()]
        }
        FnDerivativeAtSelected => {
            req.push(rt.derivative_existence(f.clone(), point.clone()));
            let value: Obj = DerivativeAt::new(f.clone(), point.clone()).into();
            vec![rt.derivative_candidate(f, point, value).into()]
        }
        FnDerivativeAtUnique => {
            req.push(
                rt.derivative_candidate(f.clone(), point.clone(), args[2].clone())
                    .into(),
            );
            req.push(rt.derivative_candidate(f, point, args[3].clone()).into());
            vec![equal(rt, args[2].clone(), args[3].clone()).into()]
        }
        FnDerivativeAtConstant | FnDerivativeAtIdentity => {
            req.push(rt.derivative_interior_condition(df.clone(), point.clone()));
            let x = rt.fresh_internal_param();
            let value = if id == FnDerivativeAtIdentity {
                identifier(&x)
            } else {
                args[2].clone()
            };
            if id == FnDerivativeAtConstant {
                req.push(atomic_in(rt, value.clone(), real).into());
            }
            let eq = equal(rt, call(f.clone(), identifier(&x)), value);
            req.push(forall(rt, x, df, vec![], vec![eq]));
            vec![rt
                .derivative_candidate(
                    f,
                    point,
                    number(if id == FnDerivativeAtIdentity {
                        "1"
                    } else {
                        "0"
                    }),
                )
                .into()]
        }
        _ => {
            let out = args[if binary { 2 } else { 1 }].clone();
            let Some((r, dout)) = super::continuity::context(rt, &out)? else {
                return Ok(Err("output requires a complete unary real domain".into()));
            };
            req.extend(r);
            req.push(atomic_in(rt, point.clone(), dout.clone()).into());
            req.push(subset(rt, dout.clone(), df).into());
            req.push(rt.derivative_interior_condition(dout.clone(), point.clone()));
            let l = args[if binary { 4 } else { 3 }].clone();
            req.push(
                rt.derivative_candidate(f.clone(), point.clone(), l.clone())
                    .into(),
            );
            let x = rt.fresh_internal_param();
            let fx = call(f.clone(), identifier(&x));
            let fp = call(f.clone(), point.clone());
            let (expression, value) = if binary {
                let g = args[1].clone();
                let m = args[5].clone();
                let Some((r, dg)) = super::continuity::context(rt, &g)? else {
                    return Ok(Err(
                        "second input requires a complete unary real domain".into()
                    ));
                };
                req.extend(r);
                if id == FnDerivativeAtCompose {
                    req.push(
                        rt.derivative_candidate(g.clone(), fp.clone(), m.clone())
                            .into(),
                    );
                    let z = rt.fresh_internal_param();
                    let image = call(f.clone(), identifier(&z));
                    let member = atomic_in(rt, image, dg);
                    req.push(forall(rt, z, dout.clone(), vec![], vec![member]));
                    (call(g, fx), mul_objs(m, l))
                } else {
                    req.push(subset(rt, dout.clone(), dg).into());
                    req.push(
                        rt.derivative_candidate(g.clone(), point.clone(), m.clone())
                            .into(),
                    );
                    let gx = call(g.clone(), identifier(&x));
                    let gp = call(g, point.clone());
                    match id {
                        FnDerivativeAtAdd => (add_objs(fx, gx), add_objs(l, m)),
                        FnDerivativeAtSubtract => (sub_objs(fx, gx), sub_objs(l, m)),
                        FnDerivativeAtMultiply => {
                            (mul_objs(fx, gx), add_objs(mul_objs(l, gp), mul_objs(fp, m)))
                        }
                        _ => {
                            req.push(
                                NotEqualFact {
                                    fact_id: rt.global_ids.allocate_fact_id(),
                                    left: gp.clone(),
                                    right: number("0"),
                                    line_file: None,
                                }
                                .into(),
                            );
                            let numerator = sub_objs(mul_objs(l, gp.clone()), mul_objs(fp, m));
                            (
                                div_objs(fx, gx),
                                div_objs(div_objs(numerator, gp.clone()), gp),
                            )
                        }
                    }
                }
            } else {
                match id {
                    FnDerivativeAtNeg => (
                        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(fx) })),
                        Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(l) })),
                    ),
                    FnDerivativeAtScale => {
                        let c = args[4].clone();
                        req.push(atomic_in(rt, c.clone(), real).into());
                        (mul_objs(c.clone(), fx), mul_objs(c, l))
                    }
                    FnDerivativeAtPower => {
                        let n = args[4].clone();
                        req.push(atomic_in(rt, n.clone(), Obj::StandardSet(StandardSet::N)).into());
                        let index = sub_objs(
                            Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
                                left: Box::new(n.clone()),
                                right: Box::new(number("1")),
                            })),
                            number("1"),
                        );
                        let factor = Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                            base: Box::new(fp),
                            exponent: Box::new(index),
                        }));
                        (
                            Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
                                base: Box::new(fx),
                                exponent: Box::new(n.clone()),
                            })),
                            mul_objs(mul_objs(n, factor), l),
                        )
                    }
                    _ => unreachable!("registered derivative laws"),
                }
            };
            let equation = equal(rt, call(out.clone(), identifier(&x)), expression);
            req.push(forall(rt, x, dout, vec![], vec![equation]));
            vec![rt.derivative_candidate(out, point, value).into()]
        }
    };
    Ok(Ok((req, result)))
}
