//! Explicit real-sequence limit theorems. Each returned law retains checked premises.
use super::helper::*;
use crate::ast::param::{SetBoundParameterGroup, SetBoundParameterList};
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::sequence_limit::sequence_membership;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, div_objs, mul_objs, sub_objs};

pub(super) fn prepare_sequence_limits(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> Result<(Vec<Fact>, Vec<Fact>), String> {
    use BuiltinTheoremId::*;
    let a = args[0].clone();
    let mut requirements = vec![sequence_membership(rt, a.clone())];
    let conclusions = match id {
        SequenceLimitFromEpsilon => {
            let l = args[1].clone();
            requirements.push(atomic_in(rt, l.clone(), real()).into());
            requirements.push(rt.sequence_limit_epsilon_fact(a.clone(), l.clone()));
            vec![candidate(rt, a, l)]
        }
        SequenceLimitTail => {
            let (l, epsilon) = (args[1].clone(), args[2].clone());
            requirements.push(candidate(rt, a.clone(), l.clone()));
            requirements
                .push(atomic_in(rt, epsilon.clone(), Obj::StandardSet(StandardSet::RPos)).into());
            let n = rt.fresh_internal_param();
            let tail = rt.sequence_limit_tail_fact(a, l, epsilon, identifier(&n));
            vec![exist(rt, typed(n, nat_pos()), vec![tail.into()], false)]
        }
        SequenceLimitConstant => {
            let l = args[1].clone();
            requirements.push(atomic_in(rt, l.clone(), real()).into());
            let n = rt.fresh_internal_param();
            let equation = equal(rt, call(&a, identifier(&n)), l.clone());
            requirements.push(forall(rt, n, nat_pos(), vec![], vec![equation]));
            vec![candidate(rt, a, l)]
        }
        SequenceLimitNeg | SequenceLimitAbs => {
            let l = args[1].clone();
            requirements.push(candidate(rt, a.clone(), l.clone()));
            let (sequence, value) = if id == SequenceLimitNeg {
                (seq(rt, |n| neg(call(&a, n))), neg(l))
            } else {
                (seq(rt, |n| abs(call(&a, n))), abs(l))
            };
            vec![candidate(rt, sequence, value)]
        }
        SequenceLimitScale | SequenceLimitPower => {
            let (l, c) = (args[1].clone(), args[2].clone());
            requirements.push(candidate(rt, a.clone(), l.clone()));
            requirements.push(
                atomic_in(
                    rt,
                    c.clone(),
                    if id == SequenceLimitPower {
                        Obj::StandardSet(StandardSet::N)
                    } else {
                        real()
                    },
                )
                .into(),
            );
            let (sequence, value) = if id == SequenceLimitPower {
                (seq(rt, |n| power(call(&a, n), c.clone())), power(l, c))
            } else {
                (
                    seq(rt, |n| mul_objs(c.clone(), call(&a, n))),
                    mul_objs(c, l),
                )
            };
            vec![candidate(rt, sequence, value)]
        }
        SequenceLimitAdd | SequenceLimitSubtract | SequenceLimitMultiply | SequenceLimitDivide => {
            let (b, l, m) = (args[1].clone(), args[2].clone(), args[3].clone());
            requirements.push(sequence_membership(rt, b.clone()));
            requirements.push(candidate(rt, a.clone(), l.clone()));
            requirements.push(candidate(rt, b.clone(), m.clone()));
            if id == SequenceLimitDivide {
                requirements.push(not_equal(rt, m.clone(), number("0")).into());
                // A nonzero limiting denominator does not make its early terms nonzero.
                let n = rt.fresh_internal_param();
                let nonzero = not_equal(rt, call(&b, identifier(&n)), number("0"));
                requirements.push(forall(rt, n, nat_pos(), vec![], vec![nonzero]));
            }
            let combine = |x, y| match id {
                SequenceLimitAdd => add_objs(x, y),
                SequenceLimitSubtract => sub_objs(x, y),
                SequenceLimitMultiply => mul_objs(x, y),
                SequenceLimitDivide => div_objs(x, y),
                _ => unreachable!("binary sequence law"),
            };
            let sequence = seq(rt, |n| combine(call(&a, n.clone()), call(&b, n)));
            vec![candidate(rt, sequence, combine(l, m))]
        }
        SequenceLimitEventuallyEqual => {
            let (b, l, n0) = (args[1].clone(), args[2].clone(), args[3].clone());
            requirements.push(sequence_membership(rt, b.clone()));
            requirements.push(candidate(rt, a.clone(), l.clone()));
            requirements.push(atomic_in(rt, n0.clone(), nat_pos()).into());
            let n = rt.fresh_internal_param();
            let guard = greater_equal(rt, identifier(&n), n0);
            let equation = equal(rt, call(&a, identifier(&n)), call(&b, identifier(&n)));
            requirements.push(forall(rt, n, nat_pos(), vec![guard], vec![equation]));
            vec![candidate(rt, b, l)]
        }
        SequenceLimitShift => {
            let (l, m) = (args[1].clone(), args[2].clone());
            requirements.push(candidate(rt, a.clone(), l.clone()));
            requirements.push(atomic_in(rt, m.clone(), Obj::StandardSet(StandardSet::N)).into());
            let sequence = seq(rt, |n| call(&a, add_objs(n, m.clone())));
            vec![candidate(rt, sequence, l)]
        }
        SequenceLimitCompare => {
            let (b, l, m, n0) = (
                args[1].clone(),
                args[2].clone(),
                args[3].clone(),
                args[4].clone(),
            );
            requirements.push(candidate(rt, a.clone(), l.clone()));
            requirements.push(candidate(rt, b.clone(), m.clone()));
            requirements.push(atomic_in(rt, n0.clone(), nat_pos()).into());
            let n = rt.fresh_internal_param();
            let guard = greater_equal(rt, identifier(&n), n0);
            let bound = le(rt, call(&a, identifier(&n)), call(&b, identifier(&n)));
            requirements.push(forall(rt, n, nat_pos(), vec![guard], vec![bound]));
            vec![le(rt, l, m).into()]
        }
        SequenceLimitSqueeze => {
            let (b, c, l, n0) = (
                args[1].clone(),
                args[2].clone(),
                args[3].clone(),
                args[4].clone(),
            );
            requirements.push(sequence_membership(rt, b.clone()));
            requirements.push(candidate(rt, a.clone(), l.clone()));
            requirements.push(candidate(rt, c.clone(), l.clone()));
            requirements.push(atomic_in(rt, n0.clone(), nat_pos()).into());
            let n = rt.fresh_internal_param();
            let guard = greater_equal(rt, identifier(&n), n0);
            let lower = le(rt, call(&a, identifier(&n)), call(&b, identifier(&n)));
            let upper = le(rt, call(&b, identifier(&n)), call(&c, identifier(&n)));
            requirements.push(forall(rt, n, nat_pos(), vec![guard], vec![lower, upper]));
            vec![candidate(rt, b, l)]
        }
        SequenceLimitUnique => {
            let (l, m) = (args[1].clone(), args[2].clone());
            requirements.push(candidate(rt, a.clone(), l.clone()));
            requirements.push(candidate(rt, a, m.clone()));
            vec![equal(rt, l, m).into()]
        }
        SequenceLimitExists => {
            let l = args[1].clone();
            requirements.push(candidate(rt, a.clone(), l));
            vec![rt.sequence_limit_existence(a)]
        }
        SequenceLimitSelected => {
            requirements.push(rt.sequence_limit_existence(a.clone()));
            let value: Obj = SequenceLimit::new(a.clone()).into();
            vec![candidate(rt, a, value)]
        }
        _ => return Err("Not a sequence-limit theorem".into()),
    };
    Ok((requirements, conclusions))
}

fn candidate(rt: &mut Runtime, a: Obj, l: Obj) -> Fact {
    rt.sequence_limit_candidate(a, l).into()
}
fn real() -> Obj {
    Obj::StandardSet(StandardSet::R)
}
fn nat_pos() -> Obj {
    Obj::StandardSet(StandardSet::NPos)
}
fn call(a: &Obj, n: Obj) -> Obj {
    crate::execute::execute_fact_stmt::function_domain::function_application(a, vec![Box::new(n)])
        .expect("one argument call")
}
fn seq(rt: &mut Runtime, body: impl FnOnce(Obj) -> Obj) -> Obj {
    let n = rt.fresh_internal_param();
    let value = body(identifier(&n));
    Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
        body: FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![n],
                    param_type: Box::new(nat_pos()),
                }],
            },
            dom_facts: vec![],
            ret_set: Box::new(real()),
        },
        equal_to: Box::new(value),
    }))
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
fn greater_equal(rt: &mut Runtime, left: Obj, right: Obj) -> Fact {
    GreaterEqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
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
