//! Explicit finite-approach limit laws with checked complete domains and named outputs.
use super::helper::*;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::function_limit::{
    function_limit_exists, function_limit_forall,
};
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};

pub(super) fn prepare_function_limits(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    if matches!(
        id,
        FnLimitAtToLeft | FnLimitAtToRight | FnLimitFromSides | FnLimitSidesMismatch
    ) {
        return prepare_function_limit_bridges(rt, id, args);
    }
    let infinite = infinity_limit_schema(id);
    let (id, make_approach) =
        function_limit_schema(infinite.as_ref().map(|(base, _)| *base).unwrap_or(id));
    if id == FnLimitAtRealAccumulation {
        let approach = infinite
            .map(|(_, a)| a)
            .unwrap_or_else(|| make_approach(args[0].clone()));
        let requirements = match approach.point() {
            Some(p) => vec![atomic_in(rt, p.clone(), real()).into()],
            None => vec![],
        };
        let accumulation = rt.function_limit_accumulation(real(), approach);
        return Ok(Ok((requirements, vec![accumulation])));
    }
    let f = args[0].clone();
    let Some((mut requirements, domain)) = context(rt, &f)? else {
        return Ok(Err(
            "requires an unambiguous complete unary real function domain".into(),
        ));
    };
    let point_index = match id {
        FnLimitAtNeg | FnLimitAtAbs | FnLimitAtScale | FnLimitAtPower | FnLimitAtLocalEqual
        | FnLimitAtCompare => 2,
        FnLimitAtAdd | FnLimitAtSubtract | FnLimitAtMultiply | FnLimitAtDivide
        | FnLimitAtSqueeze => 3,
        _ => 1,
    };
    let is_infinite = infinite.is_some();
    let approach = infinite
        .map(|(_, a)| a)
        .unwrap_or_else(|| make_approach(args[point_index].clone()));
    let threshold_set = approach.threshold_set();
    if let Some(point) = approach.point() {
        requirements.push(atomic_in(rt, point.clone(), real()).into());
    }
    // Stable finite-call roles; infinity calls omit only the point role.
    let arg = |index: usize| {
        &args[if is_infinite && index > point_index {
            index - 1
        } else {
            index
        }]
    };
    let conclusions = match id {
        FnLimitAtFromEpsilon => {
            let value = arg(2).clone();
            requirements.push(atomic_in(rt, value.clone(), real()).into());
            requirements.push(rt.function_limit_accumulation(domain.clone(), approach.clone()));
            requirements.push(rt.function_limit_epsilon(
                f.clone(),
                domain,
                approach.clone(),
                value.clone(),
            ));
            vec![candidate(rt, f, approach, value)]
        }
        FnLimitAtAccumulation => {
            requirements.push(candidate(rt, f.clone(), approach.clone(), arg(2).clone()));
            vec![rt.function_limit_accumulation(domain, approach)]
        }
        FnLimitAtControl => {
            let (value, epsilon) = (arg(2).clone(), arg(3).clone());
            requirements.push(candidate(rt, f.clone(), approach.clone(), value.clone()));
            requirements.push(atomic_in(rt, epsilon.clone(), positive_real()).into());
            let delta = rt.fresh_internal_param();
            let inclusion =
                rt.function_limit_control(f, domain, approach, value, epsilon, identifier(&delta));
            vec![function_limit_exists(
                rt,
                delta,
                threshold_set.clone(),
                vec![inclusion],
            )]
        }
        FnLimitAtConstant | FnLimitAtIdentity => {
            let value = if id == FnLimitAtIdentity {
                approach
                    .point()
                    .expect("identity has a finite approach point")
                    .clone()
            } else {
                arg(2).clone()
            };
            requirements.push(atomic_in(rt, value.clone(), real()).into());
            requirements.push(rt.function_limit_accumulation(domain.clone(), approach.clone()));
            let x = rt.fresh_internal_param();
            let rhs = if id == FnLimitAtIdentity {
                identifier(&x)
            } else {
                value.clone()
            };
            let equation = equal(rt, call(&f, identifier(&x)), rhs);
            requirements.push(forall(rt, x, domain, vec![], vec![equation]));
            vec![candidate(rt, f, approach, value)]
        }
        FnLimitAtUnique => {
            let (a, b) = (arg(2).clone(), arg(3).clone());
            requirements.push(candidate(rt, f.clone(), approach.clone(), a.clone()));
            requirements.push(candidate(rt, f, approach, b.clone()));
            vec![equal(rt, a, b).into()]
        }
        FnLimitAtExists => {
            requirements.push(candidate(rt, f.clone(), approach.clone(), arg(2).clone()));
            vec![rt.function_limit_existence(f, approach)]
        }
        FnLimitAtSelected => {
            requirements.push(rt.function_limit_existence(f.clone(), approach.clone()));
            let value: Obj = FunctionLimit::with_approach(f.clone(), approach.clone()).into();
            vec![candidate(rt, f, approach, value)]
        }
        FnLimitAtNeg | FnLimitAtAbs | FnLimitAtScale | FnLimitAtPower => {
            let (output, value) = (arg(1).clone(), arg(3).clone());
            let Some((output_requirements, output_domain)) = context(rt, &output)? else {
                return Ok(Err("result must be a complete unary real function".into()));
            };
            requirements.extend(output_requirements);
            requirements.push(equal(rt, output_domain, domain.clone()).into());
            requirements.push(candidate(rt, f.clone(), approach.clone(), value.clone()));
            let parameter = if matches!(id, FnLimitAtScale | FnLimitAtPower) {
                arg(4).clone()
            } else {
                number("0")
            };
            if matches!(id, FnLimitAtScale | FnLimitAtPower) {
                let carrier = if id == FnLimitAtPower {
                    Obj::StandardSet(StandardSet::N)
                } else {
                    real()
                };
                requirements.push(atomic_in(rt, parameter.clone(), carrier).into());
            }
            let operation = |x| match id {
                FnLimitAtNeg => neg(x),
                FnLimitAtAbs => abs(x),
                FnLimitAtScale => mul_objs(parameter.clone(), x),
                FnLimitAtPower => power(x, parameter.clone()),
                _ => unreachable!("unary limit law"),
            };
            let x = rt.fresh_internal_param();
            let equation = equal(
                rt,
                call(&output, identifier(&x)),
                operation(call(&f, identifier(&x))),
            );
            requirements.push(forall(rt, x, domain, vec![], vec![equation]));
            vec![candidate(rt, output, approach, operation(value))]
        }
        FnLimitAtAdd | FnLimitAtSubtract | FnLimitAtMultiply | FnLimitAtDivide => {
            let (g, output, a, b) = (
                arg(1).clone(),
                arg(2).clone(),
                arg(4).clone(),
                arg(5).clone(),
            );
            for function in [&g, &output] {
                let Some((extra, other_domain)) = context(rt, function)? else {
                    return Ok(Err(
                        "operands and result must be complete unary real functions".into(),
                    ));
                };
                requirements.extend(extra);
                requirements.push(equal(rt, other_domain, domain.clone()).into());
            }
            requirements.push(candidate(rt, f.clone(), approach.clone(), a.clone()));
            requirements.push(candidate(rt, g.clone(), approach.clone(), b.clone()));
            if id == FnLimitAtDivide {
                requirements.push(not_equal(rt, b.clone(), number("0")).into());
                let x = rt.fresh_internal_param();
                let nonzero = not_equal(rt, call(&g, identifier(&x)), number("0"));
                requirements.push(forall(rt, x, domain.clone(), vec![], vec![nonzero]));
            }
            let operation = |x, y| match id {
                FnLimitAtAdd => add_objs(x, y),
                FnLimitAtSubtract => sub_objs(x, y),
                FnLimitAtMultiply => mul_objs(x, y),
                FnLimitAtDivide => div_objs(x, y),
                _ => unreachable!("binary limit law"),
            };
            let x = rt.fresh_internal_param();
            let equation = equal(
                rt,
                call(&output, identifier(&x)),
                operation(call(&f, identifier(&x)), call(&g, identifier(&x))),
            );
            requirements.push(forall(rt, x, domain, vec![], vec![equation]));
            vec![candidate(rt, output, approach, operation(a, b))]
        }
        FnLimitAtLocalEqual => {
            let (output, value, radius) = (arg(1).clone(), arg(3).clone(), arg(4).clone());
            let Some((extra, output_domain)) = context(rt, &output)? else {
                return Ok(Err("target must be a complete unary real function".into()));
            };
            requirements.extend(extra);
            requirements.push(candidate(rt, f.clone(), approach.clone(), value.clone()));
            requirements.push(atomic_in(rt, radius.clone(), threshold_set.clone()).into());
            requirements
                .push(rt.function_limit_accumulation(output_domain.clone(), approach.clone()));
            let neighborhood =
                rt.function_limit_neighborhood(output_domain, approach.clone(), radius);
            requirements.push(subset(rt, neighborhood.clone(), domain).into());
            let x = rt.fresh_internal_param();
            let equation = equal(rt, call(&output, identifier(&x)), call(&f, identifier(&x)));
            requirements.push(forall(rt, x, neighborhood, vec![], vec![equation]));
            vec![candidate(rt, output, approach, value)]
        }
        FnLimitAtCompare => {
            let (g, a, b, radius) = (
                arg(1).clone(),
                arg(3).clone(),
                arg(4).clone(),
                arg(5).clone(),
            );
            let Some((extra, other_domain)) = context(rt, &g)? else {
                return Ok(Err(
                    "comparison requires a complete unary real function".into()
                ));
            };
            requirements.extend(extra);
            requirements.push(equal(rt, other_domain, domain.clone()).into());
            requirements.push(candidate(rt, f.clone(), approach.clone(), a.clone()));
            requirements.push(candidate(rt, g.clone(), approach.clone(), b.clone()));
            requirements.push(atomic_in(rt, radius.clone(), threshold_set.clone()).into());
            let neighborhood = rt.function_limit_neighborhood(domain, approach, radius);
            let x = rt.fresh_internal_param();
            let bound = le(rt, call(&f, identifier(&x)), call(&g, identifier(&x)));
            requirements.push(forall(rt, x, neighborhood, vec![], vec![bound]));
            vec![le(rt, a, b).into()]
        }
        FnLimitAtSqueeze => {
            let (middle, upper, value, radius) = (
                arg(1).clone(),
                arg(2).clone(),
                arg(4).clone(),
                arg(5).clone(),
            );
            for function in [&middle, &upper] {
                let Some((extra, other_domain)) = context(rt, function)? else {
                    return Ok(Err("squeeze requires complete unary real functions".into()));
                };
                requirements.extend(extra);
                requirements.push(equal(rt, other_domain, domain.clone()).into());
            }
            requirements.push(candidate(rt, f.clone(), approach.clone(), value.clone()));
            requirements.push(candidate(
                rt,
                upper.clone(),
                approach.clone(),
                value.clone(),
            ));
            requirements.push(atomic_in(rt, radius.clone(), threshold_set.clone()).into());
            let neighborhood = rt.function_limit_neighborhood(domain, approach.clone(), radius);
            let x = rt.fresh_internal_param();
            let chain = ChainFact {
                fact_id: rt.global_ids.allocate_fact_id(),
                objs: vec![
                    call(&f, identifier(&x)),
                    call(&middle, identifier(&x)),
                    call(&upper, identifier(&x)),
                ],
                prop_names: vec![
                    AtomicName::Plain {
                        name: crate::parse::keywords::LESS_EQUAL.into(),
                    },
                    AtomicName::Plain {
                        name: crate::parse::keywords::LESS_EQUAL.into(),
                    },
                ],
                line_file: None,
            };
            requirements.push(function_limit_forall(
                rt,
                x,
                neighborhood,
                vec![],
                vec![Fact::ChainFact(chain)],
            ));
            vec![candidate(rt, middle, approach, value)]
        }
        FnLimitAtEventuallyPositive | FnLimitAtEventuallyNonzero => {
            let value = arg(2).clone();
            requirements.push(candidate(rt, f.clone(), approach.clone(), value.clone()));
            let (condition, target) = if id == FnLimitAtEventuallyPositive {
                (less(rt, number("0"), value), positive_real())
            } else {
                (
                    not_equal(rt, value, number("0")),
                    Obj::StandardSet(StandardSet::RStar),
                )
            };
            requirements.push(condition.into());
            let delta = rt.fresh_internal_param();
            let neighborhood = rt.function_limit_neighborhood(domain, approach, identifier(&delta));
            let inclusion = subset(rt, neighborhood, PreimageSet::new(f, target).into());
            vec![function_limit_exists(
                rt,
                delta,
                threshold_set.clone(),
                vec![inclusion],
            )]
        }
        _ => return Ok(Err("not a finite-approach function-limit theorem".into())),
    };
    Ok(Ok((requirements, conclusions)))
}

// Preparation extracts a shape; all signature/carrier premises are rechecked
// by the ordinary explicit theorem pipeline and retained in its evidence.
fn context(rt: &mut Runtime, function: &Obj) -> RuntimeResult<Option<(Vec<Fact>, Obj)>> {
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
    let requirements = vec![
        atomic_in(
            rt,
            function.clone(),
            Obj::FunctionSpace(FunctionSpace::FnSet(signature.clone())),
        )
        .into(),
        subset(rt, carrier, real()).into(),
        subset(rt, *signature.ret_set.clone(), real()).into(),
    ];
    Ok(Some((requirements, proof.domain)))
}
fn candidate(rt: &mut Runtime, f: Obj, x0: LimitApproach, value: Obj) -> Fact {
    rt.function_limit_candidate(f, x0, value).into()
}
fn real() -> Obj {
    Obj::StandardSet(StandardSet::R)
}
fn positive_real() -> Obj {
    Obj::StandardSet(StandardSet::RPos)
}
fn call(f: &Obj, x: Obj) -> Obj {
    crate::execute::execute_fact_stmt::function_domain::function_application(f, vec![Box::new(x)])
        .expect("one argument call")
}
fn neg(x: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(x) }))
}
fn abs(x: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: Box::new(x) }))
}
fn power(x: Obj, n: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Pow(Pow {
        base: Box::new(x),
        exponent: Box::new(n),
    }))
}
fn not_equal(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    NotEqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}

// The shared laws use the same checked domain equations; the complete approach
// remains in each generated premise and conclusion. No theorem runs from WD.
fn function_limit_schema(id: BuiltinTheoremId) -> (BuiltinTheoremId, fn(Obj) -> LimitApproach) {
    use BuiltinTheoremId::*;
    match id {
        FnLimitLeftRealAccumulation => (FnLimitAtRealAccumulation, |p| {
            LimitApproach::FromLeft(Box::new(p))
        }),
        FnLimitLeftFromEpsilon => (FnLimitAtFromEpsilon, |p| {
            LimitApproach::FromLeft(Box::new(p))
        }),
        FnLimitLeftControl => (FnLimitAtControl, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftAccumulation => (FnLimitAtAccumulation, |p| {
            LimitApproach::FromLeft(Box::new(p))
        }),
        FnLimitLeftConstant => (FnLimitAtConstant, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftIdentity => (FnLimitAtIdentity, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftUnique => (FnLimitAtUnique, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftExists => (FnLimitAtExists, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftSelected => (FnLimitAtSelected, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftNeg => (FnLimitAtNeg, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftAbs => (FnLimitAtAbs, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftScale => (FnLimitAtScale, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftPower => (FnLimitAtPower, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftAdd => (FnLimitAtAdd, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftSubtract => (FnLimitAtSubtract, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftMultiply => (FnLimitAtMultiply, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftDivide => (FnLimitAtDivide, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftLocalEqual => (FnLimitAtLocalEqual, |p| {
            LimitApproach::FromLeft(Box::new(p))
        }),
        FnLimitLeftCompare => (FnLimitAtCompare, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftSqueeze => (FnLimitAtSqueeze, |p| LimitApproach::FromLeft(Box::new(p))),
        FnLimitLeftEventuallyPositive => (FnLimitAtEventuallyPositive, |p| {
            LimitApproach::FromLeft(Box::new(p))
        }),
        FnLimitLeftEventuallyNonzero => (FnLimitAtEventuallyNonzero, |p| {
            LimitApproach::FromLeft(Box::new(p))
        }),
        FnLimitRightRealAccumulation => (FnLimitAtRealAccumulation, |p| {
            LimitApproach::FromRight(Box::new(p))
        }),
        FnLimitRightFromEpsilon => (FnLimitAtFromEpsilon, |p| {
            LimitApproach::FromRight(Box::new(p))
        }),
        FnLimitRightControl => (FnLimitAtControl, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightAccumulation => (FnLimitAtAccumulation, |p| {
            LimitApproach::FromRight(Box::new(p))
        }),
        FnLimitRightConstant => (FnLimitAtConstant, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightIdentity => (FnLimitAtIdentity, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightUnique => (FnLimitAtUnique, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightExists => (FnLimitAtExists, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightSelected => (FnLimitAtSelected, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightNeg => (FnLimitAtNeg, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightAbs => (FnLimitAtAbs, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightScale => (FnLimitAtScale, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightPower => (FnLimitAtPower, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightAdd => (FnLimitAtAdd, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightSubtract => (FnLimitAtSubtract, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightMultiply => (FnLimitAtMultiply, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightDivide => (FnLimitAtDivide, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightLocalEqual => (FnLimitAtLocalEqual, |p| {
            LimitApproach::FromRight(Box::new(p))
        }),
        FnLimitRightCompare => (FnLimitAtCompare, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightSqueeze => (FnLimitAtSqueeze, |p| LimitApproach::FromRight(Box::new(p))),
        FnLimitRightEventuallyPositive => (FnLimitAtEventuallyPositive, |p| {
            LimitApproach::FromRight(Box::new(p))
        }),
        FnLimitRightEventuallyNonzero => (FnLimitAtEventuallyNonzero, |p| {
            LimitApproach::FromRight(Box::new(p))
        }),
        _ => (id, |p| LimitApproach::AtPoint(Box::new(p))),
    }
}

// Relative ordinary limits restrict only to an accumulating side. Matching
// sides cover the punctured domain; unequal sides exclude every ordinary value.
fn prepare_function_limit_bridges(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let f = args[0].clone();
    let point = args[1].clone();
    let value = args[2].clone();
    let Some((mut requirements, domain)) = context(rt, &f)? else {
        return Ok(Err(
            "requires an unambiguous complete unary real domain".into()
        ));
    };
    requirements.push(atomic_in(rt, point.clone(), real()).into());
    requirements.push(atomic_in(rt, value.clone(), real()).into());
    let at = LimitApproach::AtPoint(Box::new(point.clone()));
    let left = LimitApproach::FromLeft(Box::new(point.clone()));
    let right = LimitApproach::FromRight(Box::new(point));
    let conclusions = match id {
        FnLimitAtToLeft | FnLimitAtToRight => {
            let side = if id == FnLimitAtToLeft { left } else { right };
            requirements.push(candidate(rt, f.clone(), at, value.clone()));
            requirements.push(rt.function_limit_accumulation(domain, side.clone()));
            vec![candidate(rt, f, side, value)]
        }
        FnLimitFromSides => {
            requirements.push(candidate(rt, f.clone(), left, value.clone()));
            requirements.push(candidate(rt, f.clone(), right, value.clone()));
            vec![candidate(rt, f, at, value)]
        }
        FnLimitSidesMismatch => {
            let other = args[3].clone();
            requirements.push(candidate(rt, f.clone(), left, value.clone()));
            requirements.push(candidate(rt, f.clone(), right, other.clone()));
            requirements.push(not_equal(rt, value, other).into());
            let l = rt.fresh_internal_param();
            let positive = rt.function_limit_candidate(f, at, identifier(&l));
            let negative = crate::ast::fact::negate_atomic_fact(
                &positive.into(),
                rt.global_ids.allocate_fact_id(),
            )
            .expect("candidate has mathematical negation");
            vec![function_limit_forall(
                rt,
                l,
                real(),
                vec![],
                vec![negative.into()],
            )]
        }
        _ => unreachable!("explicit bridge dispatcher"),
    };
    Ok(Ok((requirements, conclusions)))
}

fn infinity_limit_schema(id: BuiltinTheoremId) -> Option<(BuiltinTheoremId, LimitApproach)> {
    use BuiltinTheoremId::*;
    match id {
        FnLimitPosInfRealAccumulation => {
            Some((FnLimitAtRealAccumulation, LimitApproach::AtPositiveInfinity))
        }
        FnLimitPosInfFromEpsilon => Some((FnLimitAtFromEpsilon, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfControl => Some((FnLimitAtControl, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfAccumulation => {
            Some((FnLimitAtAccumulation, LimitApproach::AtPositiveInfinity))
        }
        FnLimitPosInfConstant => Some((FnLimitAtConstant, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfUnique => Some((FnLimitAtUnique, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfExists => Some((FnLimitAtExists, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfSelected => Some((FnLimitAtSelected, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfNeg => Some((FnLimitAtNeg, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfAbs => Some((FnLimitAtAbs, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfScale => Some((FnLimitAtScale, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfPower => Some((FnLimitAtPower, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfAdd => Some((FnLimitAtAdd, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfSubtract => Some((FnLimitAtSubtract, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfMultiply => Some((FnLimitAtMultiply, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfDivide => Some((FnLimitAtDivide, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfLocalEqual => Some((FnLimitAtLocalEqual, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfCompare => Some((FnLimitAtCompare, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfSqueeze => Some((FnLimitAtSqueeze, LimitApproach::AtPositiveInfinity)),
        FnLimitPosInfEventuallyPositive => Some((
            FnLimitAtEventuallyPositive,
            LimitApproach::AtPositiveInfinity,
        )),
        FnLimitPosInfEventuallyNonzero => Some((
            FnLimitAtEventuallyNonzero,
            LimitApproach::AtPositiveInfinity,
        )),
        FnLimitNegInfRealAccumulation => {
            Some((FnLimitAtRealAccumulation, LimitApproach::AtNegativeInfinity))
        }
        FnLimitNegInfFromEpsilon => Some((FnLimitAtFromEpsilon, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfControl => Some((FnLimitAtControl, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfAccumulation => {
            Some((FnLimitAtAccumulation, LimitApproach::AtNegativeInfinity))
        }
        FnLimitNegInfConstant => Some((FnLimitAtConstant, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfUnique => Some((FnLimitAtUnique, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfExists => Some((FnLimitAtExists, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfSelected => Some((FnLimitAtSelected, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfNeg => Some((FnLimitAtNeg, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfAbs => Some((FnLimitAtAbs, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfScale => Some((FnLimitAtScale, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfPower => Some((FnLimitAtPower, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfAdd => Some((FnLimitAtAdd, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfSubtract => Some((FnLimitAtSubtract, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfMultiply => Some((FnLimitAtMultiply, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfDivide => Some((FnLimitAtDivide, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfLocalEqual => Some((FnLimitAtLocalEqual, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfCompare => Some((FnLimitAtCompare, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfSqueeze => Some((FnLimitAtSqueeze, LimitApproach::AtNegativeInfinity)),
        FnLimitNegInfEventuallyPositive => Some((
            FnLimitAtEventuallyPositive,
            LimitApproach::AtNegativeInfinity,
        )),
        FnLimitNegInfEventuallyNonzero => Some((
            FnLimitAtEventuallyNonzero,
            LimitApproach::AtNegativeInfinity,
        )),
        _ => None,
    }
}
