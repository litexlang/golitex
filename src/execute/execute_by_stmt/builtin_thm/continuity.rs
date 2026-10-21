//! Explicit laws for native real analysis properties. Requirements are checked
//! by the ordinary theorem pipeline; constructing a schema never proves them.
#[cfg(test)]
#[path = "../../../../tests/unit/execute/real_analysis_continuity/native.rs"]
mod native_analysis_contract_tests;
#[cfg(test)]
#[path = "../../../../tests/unit/execute/real_analysis_continuity/representation.rs"]
mod representation_contract_tests;
use super::helper::*;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::function_limit::function_limit_exists;
use crate::execute::execute_fact_stmt::real_analysis::analysis_apply as call;
use crate::execute::execute_fact_stmt::sequence_limit::sequence_membership;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};

pub(super) fn prepare_analysis(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    if matches!(
        id,
        SequenceMonotoneBoundedAbove
            | SequenceMonotoneBoundedBelow
            | SequenceCauchyBounded
            | SequenceCauchyConvergent
            | SequenceConvergentBounded
    ) {
        let a = args[0].clone();
        let mut req = vec![sequence_membership(rt, a.clone())];
        use SequenceAnalysisProperty::*;
        let out = match id {
            SequenceMonotoneBoundedAbove | SequenceMonotoneBoundedBelow => {
                let increasing = id == SequenceMonotoneBoundedAbove;
                req.push(seq(
                    rt,
                    a.clone(),
                    if increasing {
                        Nondecreasing
                    } else {
                        Nonincreasing
                    },
                ));
                req.push(seq(
                    rt,
                    a.clone(),
                    if increasing {
                        BoundedAbove
                    } else {
                        BoundedBelow
                    },
                ));
                rt.sequence_limit_existence(a)
            }
            SequenceCauchyBounded | SequenceCauchyConvergent => {
                req.push(seq(rt, a.clone(), Cauchy));
                seq(
                    rt,
                    a,
                    if id == SequenceCauchyBounded {
                        Bounded
                    } else {
                        Convergent
                    },
                )
            }
            SequenceConvergentBounded => {
                req.push(seq(rt, a.clone(), Convergent));
                seq(rt, a, Bounded)
            }
            _ => unreachable!(),
        };
        return Ok(Ok((req, vec![out])));
    }
    if matches!(
        id,
        RealSupremumExists | RealInfimumExists | RealSupremumSelected | RealInfimumSelected
    ) {
        let set = args[0].clone();
        let upper = matches!(id, RealSupremumExists | RealSupremumSelected);
        let direction = if upper {
            RealBoundDirection::Upper
        } else {
            RealBoundDirection::Lower
        };
        let mut req = vec![subset(rt, set.clone(), real()).into()];
        let out = if matches!(id, RealSupremumExists | RealInfimumExists) {
            req.push(nonempty(rt, set.clone()).into());
            req.push(
                RealSetBoundedFact {
                    fact_id: rt.global_ids.allocate_fact_id(),
                    set: set.clone(),
                    boundedness: if upper {
                        RealBoundedness::Above
                    } else {
                        RealBoundedness::Below
                    },
                    line_file: None,
                }
                .into(),
            );
            rt.real_bound_existence(set, direction)
        } else {
            req.push(rt.real_bound_existence(set.clone(), direction));
            let selected = if upper {
                Supremum {
                    set: Box::new(set.clone()),
                }
                .into()
            } else {
                Infimum {
                    set: Box::new(set.clone()),
                }
                .into()
            };
            rt.real_bound_certificate(set, selected, direction).into()
        };
        return Ok(Ok((req, vec![out])));
    }
    if matches!(
        id,
        SequenceCauchyFromEpsilon
            | SequenceCauchyTail
            | SequenceConvergentFromLimit
            | SequenceLimitFromConvergent
            | SequenceStrictIncreasingNondecreasing
            | SequenceStrictDecreasingNonincreasing
            | SequenceBoundedFromBounds
            | SequenceConstantProperties
            | SequenceLimitCauchy
    ) {
        return Ok(prepare_sequence(rt, id, args));
    }
    if matches!(id, FnLimitAtContinuousCompose | FnLimitAtPuncturedCompose) {
        return prepare_limit_composition(rt, id, args);
    }
    let (base, side) = side_schema(id);
    let f = args[0].clone();
    let Some((mut req, domain)) = context(rt, &f)? else {
        return Ok(Err(
            "requires a complete unary real function, including its guards".into(),
        ));
    };
    let point_rule = matches!(
        base,
        FnContinuousAtFromEpsilon
            | FnContinuousAtControl
            | FnContinuousAtConstant
            | FnContinuousAtIdentity
            | FnContinuousAtFromLimit
            | FnContinuousAtToLimit
            | FnContinuousAtNeg
            | FnContinuousAtAbs
            | FnContinuousAtScale
            | FnContinuousAtPower
            | FnContinuousAtAdd
            | FnContinuousAtSubtract
            | FnContinuousAtMultiply
            | FnContinuousAtDivide
            | FnContinuousAtCompose
    );
    let out = if point_rule {
        let index = match base {
            FnContinuousAtNeg | FnContinuousAtAbs | FnContinuousAtScale | FnContinuousAtPower => 2,
            FnContinuousAtAdd
            | FnContinuousAtSubtract
            | FnContinuousAtMultiply
            | FnContinuousAtDivide
            | FnContinuousAtCompose => 3,
            _ => 1,
        };
        let point = args[index].clone();
        req.push(atomic_in(rt, point.clone(), domain.clone()).into());
        match base {
            FnContinuousAtFromEpsilon => {
                req.push(rt.continuity_epsilon(f.clone(), domain, point.clone(), side));
                vec![at(rt, f, point, side)]
            }
            FnContinuousAtControl => {
                req.push(at(rt, f.clone(), point.clone(), side));
                req.push(atomic_in(rt, args[2].clone(), positive()).into());
                let delta = rt.fresh_internal_param();
                let control = rt.continuity_control(
                    f,
                    domain,
                    point,
                    side,
                    args[2].clone(),
                    identifier(&delta),
                );
                vec![function_limit_exists(rt, delta, positive(), vec![control])]
            }
            FnContinuousAtConstant | FnContinuousAtIdentity => {
                let x = rt.fresh_internal_param();
                let value = if base == FnContinuousAtIdentity {
                    identifier(&x)
                } else {
                    args[2].clone()
                };
                if base == FnContinuousAtConstant {
                    req.push(atomic_in(rt, value.clone(), real()).into());
                }
                let eq = equal(rt, call(f.clone(), identifier(&x)), value);
                req.push(forall(rt, x, domain, vec![], vec![eq]));
                vec![at(rt, f, point, side)]
            }
            FnContinuousAtFromLimit => {
                let value = call(f.clone(), point.clone());
                req.push(
                    rt.function_limit_candidate(
                        f.clone(),
                        side.limit_approach(point.clone()),
                        value,
                    )
                    .into(),
                );
                vec![at(rt, f, point, side)]
            }
            FnContinuousAtToLimit => {
                req.push(at(rt, f.clone(), point.clone(), side));
                req.push(accumulation(rt, domain, point.clone(), side));
                let value = call(f.clone(), point.clone());
                vec![rt
                    .function_limit_candidate(f, side.limit_approach(point), value)
                    .into()]
            }
            FnContinuousAtCompose => {
                // f is inner, g outer, h the named output. All calls used in
                // the identity are checked on h's full domain.
                let g = args[1].clone();
                let h = args[2].clone();
                let Some((r, dg)) = context(rt, &g)? else {
                    return Ok(Err(
                        "outer function must be a complete unary real function".into()
                    ));
                };
                req.extend(r);
                let Some((r, dh)) = context(rt, &h)? else {
                    return Ok(Err("output must be a complete unary real function".into()));
                };
                req.extend(r);
                req.push(subset(rt, dh.clone(), domain).into());
                req.push(atomic_in(rt, point.clone(), dh.clone()).into());
                req.push(at(rt, f.clone(), point.clone(), side));
                req.push(at(
                    rt,
                    g.clone(),
                    call(f.clone(), point.clone()),
                    RealApproachSide::Both,
                ));
                let x = rt.fresh_internal_param();
                let fx = call(f.clone(), identifier(&x));
                let member = atomic_in(rt, fx.clone(), dg);
                req.push(forall(rt, x, dh.clone(), vec![], vec![member]));
                let x = rt.fresh_internal_param();
                let equation = equal(
                    rt,
                    call(h.clone(), identifier(&x)),
                    call(g, call(f, identifier(&x))),
                );
                req.push(forall(rt, x, dh, vec![], vec![equation]));
                vec![at(rt, h, point, side)]
            }
            _ => {
                let binary = matches!(
                    base,
                    FnContinuousAtAdd
                        | FnContinuousAtSubtract
                        | FnContinuousAtMultiply
                        | FnContinuousAtDivide
                );
                let output = args[if binary { 2 } else { 1 }].clone();
                let Some((r, dout)) = context(rt, &output)? else {
                    return Ok(Err("output must be a complete unary real function".into()));
                };
                req.extend(r);
                req.push(subset(rt, dout.clone(), domain).into());
                req.push(atomic_in(rt, point.clone(), dout.clone()).into());
                req.push(at(rt, f.clone(), point.clone(), side));
                let x = rt.fresh_internal_param();
                let fx = call(f.clone(), identifier(&x));
                let rhs = if binary {
                    let g = args[1].clone();
                    let Some((r, dg)) = context(rt, &g)? else {
                        return Ok(Err(
                            "second input must be a complete unary real function".into()
                        ));
                    };
                    req.extend(r);
                    req.push(subset(rt, dout.clone(), dg).into());
                    req.push(at(rt, g.clone(), point.clone(), side));
                    let gx = call(g.clone(), identifier(&x));
                    if base == FnContinuousAtDivide {
                        let nonzero = NotEqualFact {
                            fact_id: rt.global_ids.allocate_fact_id(),
                            left: call(g, point.clone()),
                            right: number("0"),
                            line_file: None,
                        };
                        req.push(nonzero.into());
                    }
                    match base {
                        FnContinuousAtAdd => add_objs(fx, gx),
                        FnContinuousAtSubtract => sub_objs(fx, gx),
                        FnContinuousAtMultiply => mul_objs(fx, gx),
                        _ => div_objs(fx, gx),
                    }
                } else {
                    match base {
                        FnContinuousAtNeg => neg(fx),
                        FnContinuousAtAbs => abs(fx),
                        FnContinuousAtScale => {
                            req.push(atomic_in(rt, args[3].clone(), real()).into());
                            mul_objs(args[3].clone(), fx)
                        }
                        FnContinuousAtPower => {
                            req.push(
                                atomic_in(rt, args[3].clone(), Obj::StandardSet(StandardSet::N))
                                    .into(),
                            );
                            power(fx, args[3].clone())
                        }
                        _ => unreachable!(),
                    }
                };
                let equation = equal(rt, call(output.clone(), identifier(&x)), rhs);
                req.push(forall(rt, x, dout, vec![], vec![equation]));
                vec![at(rt, output, point, side)]
            }
        }
    } else {
        match id {
            FnContinuousFromPointwise | FnUniformFromEpsilon | FnLipschitzFromEstimate => {
                let fact = match id {
                    FnContinuousFromPointwise => {
                        global(rt, f.clone(), FunctionContinuityProperty::Continuous)
                    }
                    FnUniformFromEpsilon => {
                        global(rt, f.clone(), FunctionContinuityProperty::UniformContinuous)
                    }
                    _ => lipschitz(rt, f.clone(), args[1].clone()),
                };
                let Fact::AtomicFact(ref atom) = fact else {
                    unreachable!();
                };
                let clauses = rt
                    .real_analysis_defining_clauses(
                        atom,
                        VerifyState::new(VerifyStateLevel::BuiltinRule),
                    )?
                    .expect("native property definition");
                req.extend(clauses);
                vec![fact]
            }
            FnContinuousAt => {
                req.push(global(
                    rt,
                    f.clone(),
                    FunctionContinuityProperty::Continuous,
                ));
                req.push(atomic_in(rt, args[1].clone(), domain).into());
                vec![at(rt, f, args[1].clone(), RealApproachSide::Both)]
            }
            FnUniformControl => {
                req.push(global(
                    rt,
                    f.clone(),
                    FunctionContinuityProperty::UniformContinuous,
                ));
                req.push(atomic_in(rt, args[1].clone(), positive()).into());
                let delta = rt.fresh_internal_param();
                let control =
                    rt.uniform_continuity_control(f, domain, args[1].clone(), identifier(&delta));
                vec![function_limit_exists(rt, delta, positive(), vec![control])]
            }
            FnLipschitzUniform => {
                req.push(lipschitz(rt, f.clone(), args[1].clone()));
                vec![global(rt, f, FunctionContinuityProperty::UniformContinuous)]
            }
            FnUniformContinuous => {
                req.push(global(
                    rt,
                    f.clone(),
                    FunctionContinuityProperty::UniformContinuous,
                ));
                vec![global(rt, f, FunctionContinuityProperty::Continuous)]
            }
            FnContinuousAtToLeft | FnContinuousAtToRight => {
                req.push(at(rt, f.clone(), args[1].clone(), RealApproachSide::Both));
                let s = if id == FnContinuousAtToLeft {
                    RealApproachSide::Left
                } else {
                    RealApproachSide::Right
                };
                vec![at(rt, f, args[1].clone(), s)]
            }
            FnContinuousFromSides => {
                req.push(at(rt, f.clone(), args[1].clone(), RealApproachSide::Left));
                req.push(at(rt, f.clone(), args[1].clone(), RealApproachSide::Right));
                vec![at(rt, f, args[1].clone(), RealApproachSide::Both)]
            }
            _ => {
                let x = rt.fresh_internal_param();
                if matches!(id, FnContinuousConstant | FnContinuousLog) {
                    req.push(
                        atomic_in(
                            rt,
                            args[1].clone(),
                            if id == FnContinuousLog {
                                positive()
                            } else {
                                real()
                            },
                        )
                        .into(),
                    );
                    if id == FnContinuousLog {
                        req.push(
                            NotEqualFact {
                                fact_id: rt.global_ids.allocate_fact_id(),
                                left: args[1].clone(),
                                right: number("1"),
                                line_file: None,
                            }
                            .into(),
                        );
                    }
                }
                let value = standard_value(id, identifier(&x), args.get(1).cloned())
                    .expect("registered standard continuity law");
                let equation = equal(rt, call(f.clone(), identifier(&x)), value);
                // WD of this quantified identity checks every true operator domain,
                // e.g. sqrt x>=0, ln x>0, and every denominator nonzero.
                req.push(forall(rt, x, domain, vec![], vec![equation]));
                vec![global(rt, f, FunctionContinuityProperty::Continuous)]
            }
        }
    };
    Ok(Ok((req, out)))
}

fn prepare_sequence(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> Result<(Vec<Fact>, Vec<Fact>), String> {
    use BuiltinTheoremId::*;
    use SequenceAnalysisProperty::*;
    let a = args[0].clone();
    let mut req = vec![sequence_membership(rt, a.clone())];
    let out = match id {
        SequenceCauchyFromEpsilon => {
            let fact = seq(rt, a.clone(), Cauchy);
            let Fact::AtomicFact(AtomicFact::SequenceAnalysisFact(f)) = &fact else {
                unreachable!()
            };
            // The sequence signature was checked by the theorem pipeline.
            req.extend(rt.sequence_analysis_clauses(f));
            vec![fact]
        }
        SequenceCauchyTail => {
            req.push(seq(rt, a.clone(), Cauchy));
            req.push(atomic_in(rt, args[1].clone(), positive()).into());
            let n = rt.fresh_internal_param();
            let control = rt.sequence_cauchy_control(a, args[1].clone(), identifier(&n));
            vec![function_limit_exists(rt, n, natpos(), vec![control])]
        }
        SequenceConvergentFromLimit | SequenceLimitCauchy => {
            req.push(
                rt.sequence_limit_candidate(a.clone(), args[1].clone())
                    .into(),
            );
            vec![seq(
                rt,
                a,
                if id == SequenceLimitCauchy {
                    Cauchy
                } else {
                    Convergent
                },
            )]
        }
        SequenceLimitFromConvergent => {
            req.push(seq(rt, a.clone(), Convergent));
            vec![rt.sequence_limit_existence(a)]
        }
        SequenceStrictIncreasingNondecreasing | SequenceStrictDecreasingNonincreasing => {
            let increasing = id == SequenceStrictIncreasingNondecreasing;
            req.push(seq(
                rt,
                a.clone(),
                if increasing {
                    StrictlyIncreasing
                } else {
                    StrictlyDecreasing
                },
            ));
            vec![seq(
                rt,
                a,
                if increasing {
                    Nondecreasing
                } else {
                    Nonincreasing
                },
            )]
        }
        SequenceBoundedFromBounds => {
            let (l, u) = (args[1].clone(), args[2].clone());
            req.push(atomic_in(rt, l.clone(), real()).into());
            req.push(atomic_in(rt, u.clone(), real()).into());
            let n = rt.fresh_internal_param();
            let lower = le(rt, l, call(a.clone(), identifier(&n)));
            let upper = le(rt, call(a.clone(), identifier(&n)), u);
            req.push(forall(rt, n, natpos(), vec![], vec![lower, upper]));
            vec![seq(rt, a, Bounded)]
        }
        SequenceConstantProperties => {
            let c = args[1].clone();
            req.push(atomic_in(rt, c.clone(), real()).into());
            let n = rt.fresh_internal_param();
            let equation = equal(rt, call(a.clone(), identifier(&n)), c);
            req.push(forall(rt, n, natpos(), vec![], vec![equation]));
            vec![
                seq(rt, a.clone(), Nondecreasing),
                seq(rt, a.clone(), Nonincreasing),
                seq(rt, a.clone(), Bounded),
                seq(rt, a.clone(), Cauchy),
                seq(rt, a, Convergent),
            ]
        }
        _ => unreachable!(),
    };
    Ok((req, out))
}

pub(super) fn context(rt: &mut Runtime, function: &Obj) -> RuntimeResult<Option<(Vec<Fact>, Obj)>> {
    let Some(proof) = rt.checked_real_function_limit_domain(
        function,
        VerifyState::new(VerifyStateLevel::BuiltinRule),
    )?
    else {
        return Ok(None);
    };
    let signature = &proof.source.signature;
    let carrier = signature
        .set_bound_parameters
        .groups
        .iter()
        .find(|g| !g.params.is_empty())
        .unwrap()
        .param_type
        .as_ref()
        .clone();
    let req = vec![
        atomic_in(
            rt,
            function.clone(),
            Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
        )
        .into(),
        subset(rt, carrier, real()).into(),
        subset(rt, *signature.ret_set.clone(), real()).into(),
    ];
    Ok(Some((req, proof.domain)))
}
fn at(rt: &mut Runtime, function: Obj, point: Obj, side: RealApproachSide) -> Fact {
    FunctionContinuousAtFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        function,
        point,
        side,
        line_file: None,
    }
    .into()
}
fn global(rt: &mut Runtime, function: Obj, property: FunctionContinuityProperty) -> Fact {
    FunctionContinuousFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        function,
        property,
        line_file: None,
    }
    .into()
}
fn lipschitz(rt: &mut Runtime, function: Obj, constant: Obj) -> Fact {
    FunctionLipschitzFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        function,
        constant,
        line_file: None,
    }
    .into()
}
fn accumulation(rt: &mut Runtime, domain: Obj, point: Obj, side: RealApproachSide) -> Fact {
    RealAccumulationFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        domain,
        point,
        side,
        line_file: None,
    }
    .into()
}
fn seq(rt: &mut Runtime, sequence: Obj, property: SequenceAnalysisProperty) -> Fact {
    SequenceAnalysisFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        sequence,
        property,
        line_file: None,
    }
    .into()
}
fn real() -> Obj {
    Obj::StandardSet(StandardSet::R)
}
fn positive() -> Obj {
    Obj::StandardSet(StandardSet::RPos)
}
fn natpos() -> Obj {
    Obj::StandardSet(StandardSet::NPos)
}
fn neg(arg: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(arg) }))
}
fn abs(arg: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: Box::new(arg) }))
}
fn power(base: Obj, exponent: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(base),
        exponent: Box::new(exponent),
    }))
}

fn side_schema(id: BuiltinTheoremId) -> (BuiltinTheoremId, RealApproachSide) {
    use BuiltinTheoremId::*;
    match id {
        FnContinuousAtFromEpsilon => (FnContinuousAtFromEpsilon, RealApproachSide::Both),
        FnContinuousAtControl => (FnContinuousAtControl, RealApproachSide::Both),
        FnContinuousAtConstant => (FnContinuousAtConstant, RealApproachSide::Both),
        FnContinuousAtIdentity => (FnContinuousAtIdentity, RealApproachSide::Both),
        FnContinuousAtFromLimit => (FnContinuousAtFromLimit, RealApproachSide::Both),
        FnContinuousAtToLimit => (FnContinuousAtToLimit, RealApproachSide::Both),
        FnContinuousAtNeg => (FnContinuousAtNeg, RealApproachSide::Both),
        FnContinuousAtAbs => (FnContinuousAtAbs, RealApproachSide::Both),
        FnContinuousAtScale => (FnContinuousAtScale, RealApproachSide::Both),
        FnContinuousAtPower => (FnContinuousAtPower, RealApproachSide::Both),
        FnContinuousAtAdd => (FnContinuousAtAdd, RealApproachSide::Both),
        FnContinuousAtSubtract => (FnContinuousAtSubtract, RealApproachSide::Both),
        FnContinuousAtMultiply => (FnContinuousAtMultiply, RealApproachSide::Both),
        FnContinuousAtDivide => (FnContinuousAtDivide, RealApproachSide::Both),
        FnContinuousAtCompose => (FnContinuousAtCompose, RealApproachSide::Both),
        FnContinuousLeftFromEpsilon => (FnContinuousAtFromEpsilon, RealApproachSide::Left),
        FnContinuousLeftControl => (FnContinuousAtControl, RealApproachSide::Left),
        FnContinuousLeftConstant => (FnContinuousAtConstant, RealApproachSide::Left),
        FnContinuousLeftIdentity => (FnContinuousAtIdentity, RealApproachSide::Left),
        FnContinuousLeftFromLimit => (FnContinuousAtFromLimit, RealApproachSide::Left),
        FnContinuousLeftToLimit => (FnContinuousAtToLimit, RealApproachSide::Left),
        FnContinuousLeftNeg => (FnContinuousAtNeg, RealApproachSide::Left),
        FnContinuousLeftAbs => (FnContinuousAtAbs, RealApproachSide::Left),
        FnContinuousLeftScale => (FnContinuousAtScale, RealApproachSide::Left),
        FnContinuousLeftPower => (FnContinuousAtPower, RealApproachSide::Left),
        FnContinuousLeftAdd => (FnContinuousAtAdd, RealApproachSide::Left),
        FnContinuousLeftSubtract => (FnContinuousAtSubtract, RealApproachSide::Left),
        FnContinuousLeftMultiply => (FnContinuousAtMultiply, RealApproachSide::Left),
        FnContinuousLeftDivide => (FnContinuousAtDivide, RealApproachSide::Left),
        FnContinuousLeftCompose => (FnContinuousAtCompose, RealApproachSide::Left),
        FnContinuousRightFromEpsilon => (FnContinuousAtFromEpsilon, RealApproachSide::Right),
        FnContinuousRightControl => (FnContinuousAtControl, RealApproachSide::Right),
        FnContinuousRightConstant => (FnContinuousAtConstant, RealApproachSide::Right),
        FnContinuousRightIdentity => (FnContinuousAtIdentity, RealApproachSide::Right),
        FnContinuousRightFromLimit => (FnContinuousAtFromLimit, RealApproachSide::Right),
        FnContinuousRightToLimit => (FnContinuousAtToLimit, RealApproachSide::Right),
        FnContinuousRightNeg => (FnContinuousAtNeg, RealApproachSide::Right),
        FnContinuousRightAbs => (FnContinuousAtAbs, RealApproachSide::Right),
        FnContinuousRightScale => (FnContinuousAtScale, RealApproachSide::Right),
        FnContinuousRightPower => (FnContinuousAtPower, RealApproachSide::Right),
        FnContinuousRightAdd => (FnContinuousAtAdd, RealApproachSide::Right),
        FnContinuousRightSubtract => (FnContinuousAtSubtract, RealApproachSide::Right),
        FnContinuousRightMultiply => (FnContinuousAtMultiply, RealApproachSide::Right),
        FnContinuousRightDivide => (FnContinuousAtDivide, RealApproachSide::Right),
        FnContinuousRightCompose => (FnContinuousAtCompose, RealApproachSide::Right),
        _ => (id, RealApproachSide::Both),
    }
}
fn standard_value(id: BuiltinTheoremId, x: Obj, parameter: Option<Obj>) -> Option<Obj> {
    use BuiltinTheoremId::*;
    Some(match id {
        FnContinuousConstant => parameter?,
        FnContinuousIdentity => x,
        FnContinuousLog => Obj::ExpLogOperator(ExpLogOperator::Log(Log {
            base: Box::new(parameter?),
            arg: Box::new(x),
        })),
        FnContinuousExp => Obj::ExpLogOperator(ExpLogOperator::Exp(Exp { arg: Box::new(x) })),
        FnContinuousLn => Obj::ExpLogOperator(ExpLogOperator::Ln(Ln { arg: Box::new(x) })),
        FnContinuousSin => Obj::TrigOperator(TrigOperator::Sin(Sin { arg: Box::new(x) })),
        FnContinuousCos => Obj::TrigOperator(TrigOperator::Cos(Cos { arg: Box::new(x) })),
        FnContinuousTan => Obj::TrigOperator(TrigOperator::Tan(Tan { arg: Box::new(x) })),
        FnContinuousCot => Obj::TrigOperator(TrigOperator::Cot(Cot { arg: Box::new(x) })),
        FnContinuousSec => Sec { arg: Box::new(x) }.into(),
        FnContinuousCsc => Csc { arg: Box::new(x) }.into(),
        FnContinuousArcsin => Obj::TrigOperator(TrigOperator::Arcsin(Arcsin { arg: Box::new(x) })),
        FnContinuousArccos => Obj::TrigOperator(TrigOperator::Arccos(Arccos { arg: Box::new(x) })),
        FnContinuousArctan => Obj::TrigOperator(TrigOperator::Arctan(Arctan { arg: Box::new(x) })),
        FnContinuousArccot => Obj::TrigOperator(TrigOperator::Arccot(Arccot { arg: Box::new(x) })),
        FnContinuousSinh => Sinh { arg: Box::new(x) }.into(),
        FnContinuousCosh => Cosh { arg: Box::new(x) }.into(),
        FnContinuousTanh => Tanh { arg: Box::new(x) }.into(),
        FnContinuousCoth => Coth { arg: Box::new(x) }.into(),
        FnContinuousSech => Sech { arg: Box::new(x) }.into(),
        FnContinuousCsch => Csch { arg: Box::new(x) }.into(),
        FnContinuousSqrt => Obj::ExpLogOperator(ExpLogOperator::Sqrt(Sqrt { arg: Box::new(x) })),
        _ => return None,
    })
}

fn prepare_limit_composition(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    let (f, g, h, x0, y0) = (
        args[0].clone(),
        args[1].clone(),
        args[2].clone(),
        args[3].clone(),
        args[4].clone(),
    );
    let Some((mut req, df)) = context(rt, &f)? else {
        return Ok(Err("inner function domain is unavailable".into()));
    };
    let Some((r, dg)) = context(rt, &g)? else {
        return Ok(Err("outer function domain is unavailable".into()));
    };
    req.extend(r);
    let Some((r, dh)) = context(rt, &h)? else {
        return Ok(Err("output function domain is unavailable".into()));
    };
    req.extend(r);
    req.push(
        rt.function_limit_candidate(
            f.clone(),
            LimitApproach::AtPoint(Box::new(x0.clone())),
            y0.clone(),
        )
        .into(),
    );
    req.push(accumulation(
        rt,
        dh.clone(),
        x0.clone(),
        RealApproachSide::Both,
    ));
    let punctured = id == BuiltinTheoremId::FnLimitAtPuncturedCompose;
    let value = if punctured {
        req.push(
            rt.function_limit_candidate(
                g.clone(),
                LimitApproach::AtPoint(Box::new(y0.clone())),
                args[5].clone(),
            )
            .into(),
        );
        args[5].clone()
    } else {
        req.push(at(rt, g.clone(), y0.clone(), RealApproachSide::Both));
        call(g.clone(), y0.clone())
    };
    // A local mapping condition, not a global range inclusion. The outer
    // punctured-limit route additionally excludes its centre eventually.
    let radius = rt.fresh_internal_param();
    let near = rt.function_limit_neighborhood(
        dh.clone(),
        LimitApproach::AtPoint(Box::new(x0.clone())),
        identifier(&radius),
    );
    let x = rt.fresh_internal_param();
    let fx = call(f.clone(), identifier(&x));
    let mut conditions = vec![
        atomic_in(rt, identifier(&x), df),
        atomic_in(rt, fx.clone(), dg),
    ];
    if punctured {
        conditions.push(
            NotEqualFact {
                fact_id: rt.global_ids.allocate_fact_id(),
                left: fx,
                right: y0,
                line_file: None,
            }
            .into(),
        );
    }
    conditions.push(equal(
        rt,
        call(h.clone(), identifier(&x)),
        call(g, call(f, identifier(&x))),
    ));
    let allowed = Obj::SetFormer(SetFormer::SetBuilder(SetBuilder {
        param_binding: x,
        param_set: Box::new(dh),
        facts: conditions
            .into_iter()
            .map(QuantifierFreeFact::AtomicFact)
            .collect(),
    }));
    let mapping = subset(rt, near, allowed);
    req.push(function_limit_exists(rt, radius, positive(), vec![mapping]));
    let conclusion = rt
        .function_limit_candidate(h, LimitApproach::AtPoint(Box::new(x0)), value)
        .into();
    Ok(Ok((req, vec![conclusion])))
}
