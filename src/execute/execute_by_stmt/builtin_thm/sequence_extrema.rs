//! Explicit finite limsup/liminf laws. WD never invokes this theorem dispatcher.
use super::helper::*;
use crate::builtin_theorem::BuiltinTheoremId;
use crate::execute::execute_fact_stmt::sequence_extrema::SequenceExtremum;
use crate::execute::execute_fact_stmt::sequence_limit::sequence_membership;
use crate::prelude::*;
use crate::rational_expression::helper::{add_objs, mul_objs};

pub(super) fn prepare_sequence_extrema(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    use BuiltinTheoremId::*;
    let a = args[0].clone();
    let mut req = vec![sequence_membership(rt, a.clone())];
    if id == SequenceLimitFromExtrema {
        let l = args[1].clone();
        req.push(candidate(rt, a.clone(), l.clone(), SequenceExtremum::Upper));
        req.push(candidate(rt, a.clone(), l.clone(), SequenceExtremum::Lower));
        let conclusion = rt.sequence_limit_candidate(a, l);
        return Ok(Ok((req, vec![conclusion.into()])));
    }
    if id == SequenceExtremaOrder {
        let l = args[1].clone();
        let u = args[2].clone();
        req.push(candidate(rt, a.clone(), l.clone(), SequenceExtremum::Lower));
        req.push(candidate(rt, a, u.clone(), SequenceExtremum::Upper));
        return Ok(Ok((req, vec![le(rt, l, u).into()])));
    }
    let kind = match id {
        SequenceLimsupFromEpsilon
        | SequenceLimsupBound
        | SequenceLimsupHit
        | SequenceLimsupUnique
        | SequenceLimsupExists
        | SequenceLimsupSelected
        | SequenceLimsupConstant
        | SequenceLimsupFromLimit
        | SequenceLimsupCompare
        | SequenceLimsupEventuallyEqual
        | SequenceLimsupShift
        | SequenceLimsupNeg
        | SequenceLimsupAddConstant
        | SequenceLimsupScaleNonnegative
        | SequenceLimsupScaleNegative
        | SequenceLimsupAddConvergent
        | SequenceLimsupSumBound => SequenceExtremum::Upper,
        SequenceLiminfFromEpsilon
        | SequenceLiminfBound
        | SequenceLiminfHit
        | SequenceLiminfUnique
        | SequenceLiminfExists
        | SequenceLiminfSelected
        | SequenceLiminfConstant
        | SequenceLiminfFromLimit
        | SequenceLiminfCompare
        | SequenceLiminfEventuallyEqual
        | SequenceLiminfShift
        | SequenceLiminfNeg
        | SequenceLiminfAddConstant
        | SequenceLiminfScaleNonnegative
        | SequenceLiminfScaleNegative
        | SequenceLiminfAddConvergent
        | SequenceLiminfSumBound => SequenceExtremum::Lower,
        _ => return Ok(Err("not an extremal sequence theorem".into())),
    };
    let conclusions = match id {
        SequenceLimsupFromEpsilon | SequenceLiminfFromEpsilon => {
            let l = args[1].clone();
            req.push(atomic_in(rt, l.clone(), real()).into());
            let clauses = rt.sequence_extrema_clauses(a.clone(), l.clone(), kind);
            req.extend([clauses.eventual_bound, clauses.tail_hits]);
            vec![candidate(rt, a, l, kind)]
        }
        SequenceLimsupBound | SequenceLiminfBound => {
            let l = args[1].clone();
            let eps = args[2].clone();
            req.push(candidate(rt, a.clone(), l.clone(), kind));
            req.push(atomic_in(rt, eps.clone(), positive_real()).into());
            let n = rt.fresh_internal_param();
            let body = rt.sequence_extrema_bound(a, l, kind, eps, identifier(&n));
            vec![exist(rt, typed(n, nat_pos()), vec![body], false)]
        }
        SequenceLimsupHit | SequenceLiminfHit => {
            let l = args[1].clone();
            let eps = args[2].clone();
            let cutoff = args[3].clone();
            req.push(candidate(rt, a.clone(), l.clone(), kind));
            req.push(atomic_in(rt, eps.clone(), positive_real()).into());
            req.push(atomic_in(rt, cutoff.clone(), nat_pos()).into());
            vec![Fact::ExistFact(
                rt.sequence_extrema_hit(a, l, kind, eps, cutoff),
            )]
        }
        SequenceLimsupUnique | SequenceLiminfUnique => {
            let l = args[1].clone();
            let m = args[2].clone();
            req.push(candidate(rt, a.clone(), l.clone(), kind));
            req.push(candidate(rt, a, m.clone(), kind));
            vec![equal(rt, l, m).into()]
        }
        SequenceLimsupExists | SequenceLiminfExists => {
            req.push(candidate(rt, a.clone(), args[1].clone(), kind));
            vec![existence(rt, a, kind)]
        }
        SequenceLimsupSelected | SequenceLiminfSelected => {
            req.push(existence(rt, a.clone(), kind));
            let value = selected(a.clone(), kind);
            vec![candidate(rt, a, value, kind)]
        }
        SequenceLimsupConstant | SequenceLiminfConstant => {
            let l = args[1].clone();
            req.push(atomic_in(rt, l.clone(), real()).into());
            let n = rt.fresh_internal_param();
            let equation = equal(rt, call(&a, identifier(&n)), l.clone());
            req.push(forall(rt, n, nat_pos(), vec![], vec![equation]));
            vec![candidate(rt, a, l, kind)]
        }
        SequenceLimsupFromLimit | SequenceLiminfFromLimit => {
            let l = args[1].clone();
            let source = rt.sequence_limit_candidate(a.clone(), l.clone());
            req.push(source.into());
            vec![candidate(rt, a, l, kind)]
        }
        SequenceLimsupCompare | SequenceLiminfCompare => {
            let b = args[1].clone();
            let l = args[2].clone();
            let m = args[3].clone();
            let cutoff = args[4].clone();
            req.push(sequence_membership(rt, b.clone()));
            req.push(candidate(rt, a.clone(), l.clone(), kind));
            req.push(candidate(rt, b.clone(), m.clone(), kind));
            req.push(atomic_in(rt, cutoff.clone(), nat_pos()).into());
            let n = rt.fresh_internal_param();
            let after = ge(rt, identifier(&n), cutoff);
            let bound = le(rt, call(&a, identifier(&n)), call(&b, identifier(&n)));
            req.push(forall(rt, n, nat_pos(), vec![after.into()], vec![bound]));
            vec![le(rt, l, m).into()]
        }
        SequenceLimsupEventuallyEqual
        | SequenceLiminfEventuallyEqual
        | SequenceLimsupShift
        | SequenceLiminfShift => {
            let b = args[1].clone();
            let l = args[2].clone();
            let start = args[3].clone();
            req.push(sequence_membership(rt, b.clone()));
            req.push(candidate(rt, a.clone(), l.clone(), kind));
            let shift = matches!(id, SequenceLimsupShift | SequenceLiminfShift);
            req.push(
                atomic_in(
                    rt,
                    start.clone(),
                    if shift {
                        Obj::StandardSet(StandardSet::N)
                    } else {
                        nat_pos()
                    },
                )
                .into(),
            );
            let n = rt.fresh_internal_param();
            let index = identifier(&n);
            let source_index = if shift {
                add_objs(index.clone(), start.clone())
            } else {
                index.clone()
            };
            let equation = equal(rt, call(&b, index.clone()), call(&a, source_index));
            let dom = if shift {
                vec![]
            } else {
                vec![ge(rt, index, start).into()]
            };
            req.push(forall(rt, n, nat_pos(), dom, vec![equation]));
            vec![candidate(rt, b, l, kind)]
        }
        SequenceLimsupNeg
        | SequenceLiminfNeg
        | SequenceLimsupAddConstant
        | SequenceLiminfAddConstant
        | SequenceLimsupScaleNonnegative
        | SequenceLiminfScaleNonnegative
        | SequenceLimsupScaleNegative
        | SequenceLiminfScaleNegative => {
            let b = args[1].clone();
            let l = args[2].clone();
            req.push(sequence_membership(rt, b.clone()));
            req.push(candidate(rt, a.clone(), l.clone(), kind));
            let negate = matches!(id, SequenceLimsupNeg | SequenceLiminfNeg);
            let addition = matches!(id, SequenceLimsupAddConstant | SequenceLiminfAddConstant);
            let negative_scale = matches!(
                id,
                SequenceLimsupScaleNegative | SequenceLiminfScaleNegative
            );
            let c = if negate {
                neg(number("1"))
            } else {
                args[3].clone()
            };
            req.push(atomic_in(rt, c.clone(), real()).into());
            if !negate && !addition {
                req.push(if negative_scale {
                    less(rt, c.clone(), number("0")).into()
                } else {
                    le(rt, number("0"), c.clone()).into()
                });
            }
            let operation = |v: Obj| {
                if negate {
                    neg(v)
                } else if addition {
                    add_objs(v, c.clone())
                } else {
                    mul_objs(c.clone(), v)
                }
            };
            let n = rt.fresh_internal_param();
            let equation = equal(
                rt,
                call(&b, identifier(&n)),
                operation(call(&a, identifier(&n))),
            );
            req.push(forall(rt, n, nat_pos(), vec![], vec![equation]));
            let target = if negate || negative_scale {
                opposite(kind)
            } else {
                kind
            };
            vec![candidate(rt, b, operation(l), target)]
        }
        SequenceLimsupAddConvergent
        | SequenceLiminfAddConvergent
        | SequenceLimsupSumBound
        | SequenceLiminfSumBound => {
            let b = args[1].clone();
            let h = args[2].clone();
            let l = args[3].clone();
            let m = args[4].clone();
            req.push(sequence_membership(rt, b.clone()));
            req.push(sequence_membership(rt, h.clone()));
            req.push(candidate(rt, a.clone(), l.clone(), kind));
            let bound = matches!(id, SequenceLimsupSumBound | SequenceLiminfSumBound);
            if bound {
                req.push(candidate(rt, b.clone(), m.clone(), kind));
            } else {
                let source = rt.sequence_limit_candidate(b.clone(), m.clone());
                req.push(source.into());
            }
            let n = rt.fresh_internal_param();
            let equation = equal(
                rt,
                call(&h, identifier(&n)),
                add_objs(call(&a, identifier(&n)), call(&b, identifier(&n))),
            );
            req.push(forall(rt, n, nat_pos(), vec![], vec![equation]));
            if bound {
                let c = args[5].clone();
                req.push(candidate(rt, h, c.clone(), kind));
                for (sequence, bound) in [(a, args[6].clone()), (b, args[7].clone())] {
                    req.extend(bounded(rt, sequence, bound));
                }
                let sum = add_objs(l, m);
                vec![match kind {
                    SequenceExtremum::Upper => le(rt, c, sum),
                    SequenceExtremum::Lower => le(rt, sum, c),
                }
                .into()]
            } else {
                vec![candidate(rt, h, add_objs(l, m), kind)]
            }
        }
        _ => unreachable!("extremal family dispatched above"),
    };
    Ok(Ok((req, conclusions)))
}
fn candidate(rt: &mut Runtime, a: Obj, l: Obj, kind: SequenceExtremum) -> Fact {
    match kind {
        SequenceExtremum::Upper => rt.sequence_limsup_candidate(a, l).into(),
        SequenceExtremum::Lower => rt.sequence_liminf_candidate(a, l).into(),
    }
}
fn existence(rt: &mut Runtime, a: Obj, kind: SequenceExtremum) -> Fact {
    match kind {
        SequenceExtremum::Upper => rt.sequence_limsup_existence(a),
        SequenceExtremum::Lower => rt.sequence_liminf_existence(a),
    }
}
fn selected(a: Obj, kind: SequenceExtremum) -> Obj {
    match kind {
        SequenceExtremum::Upper => SequenceLimsup::new(a).into(),
        SequenceExtremum::Lower => SequenceLiminf::new(a).into(),
    }
}
fn opposite(k: SequenceExtremum) -> SequenceExtremum {
    match k {
        SequenceExtremum::Upper => SequenceExtremum::Lower,
        SequenceExtremum::Lower => SequenceExtremum::Upper,
    }
}
fn call(f: &Obj, x: Obj) -> Obj {
    crate::execute::execute_fact_stmt::function_domain::function_application(f, vec![Box::new(x)])
        .expect("unary call")
}
fn real() -> Obj {
    Obj::StandardSet(StandardSet::R)
}
fn positive_real() -> Obj {
    Obj::StandardSet(StandardSet::RPos)
}
fn nat_pos() -> Obj {
    Obj::StandardSet(StandardSet::NPos)
}
fn neg(x: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Neg(Neg { arg: Box::new(x) }))
}
fn bounded(rt: &mut Runtime, a: Obj, m: Obj) -> Vec<Fact> {
    let n = rt.fresh_internal_param();
    let value = Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs {
        arg: Box::new(call(&a, identifier(&n))),
    }));
    let bound = le(rt, value, m.clone());
    vec![
        atomic_in(rt, m, positive_real()).into(),
        forall(rt, n, nat_pos(), vec![], vec![bound]),
    ]
}

fn ge(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    GreaterEqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}

pub(super) fn prepare_bounded_existence(
    rt: &mut Runtime,
    id: BuiltinTheoremId,
    args: &[Obj],
) -> RuntimeResult<Result<(Vec<Fact>, Vec<Fact>), String>> {
    let a = args[0].clone();
    let m = args[1].clone();
    let mut requirements = vec![sequence_membership(rt, a.clone())];
    requirements.extend(bounded(rt, a.clone(), m));
    let kind = if id == BuiltinTheoremId::SequenceLimsupBoundedExists {
        SequenceExtremum::Upper
    } else {
        SequenceExtremum::Lower
    };
    Ok(Ok((requirements, vec![existence(rt, a, kind)])))
}
