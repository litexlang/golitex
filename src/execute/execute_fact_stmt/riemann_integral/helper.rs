//! Existing objects used to state the Darboux definition; no extra AST nodes.
use super::super::real_analysis::analysis_apply;
use crate::ast::param::*;
use crate::prelude::*;
pub(crate) fn real() -> Obj {
    Obj::StandardSet(StandardSet::R)
}
pub(crate) fn num(n: &str) -> Obj {
    Obj::Literal(Literal::Number(Number::new(n.into())))
}
pub(crate) fn id(n: &crate::ast::names::BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(n))
}
pub(crate) fn min(a: Obj, b: Obj) -> Obj {
    fold_closed(Obj::ArithmeticOperator(ArithmeticOperator::Min(Min {
        left: Box::new(a),
        right: Box::new(b),
    })))
}
pub(crate) fn max(a: Obj, b: Obj) -> Obj {
    fold_closed(Obj::ArithmeticOperator(ArithmeticOperator::Max(Max {
        left: Box::new(a),
        right: Box::new(b),
    })))
}
pub(crate) fn sub(a: Obj, b: Obj) -> Obj {
    crate::rational_expression::helper::sub_objs(a, b)
}
pub(crate) fn mul(a: Obj, b: Obj) -> Obj {
    crate::rational_expression::helper::mul_objs(a, b)
}
pub(crate) fn add(a: Obj, b: Obj) -> Obj {
    crate::rational_expression::helper::add_objs(a, b)
}
pub(crate) fn abs(a: Obj) -> Obj {
    Obj::ArithmeticOperator(ArithmeticOperator::Abs(Abs { arg: Box::new(a) }))
}
pub(crate) fn interval(a: Obj, b: Obj) -> Obj {
    Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftClosedRightClosed(
        IntervalObjStruct {
            start: Box::new(a),
            end: Box::new(b),
        },
    )))
}
pub(crate) fn sorted_interval(a: Obj, b: Obj) -> Obj {
    interval(min(a.clone(), b.clone()), max(a, b))
}
pub(crate) fn open_interval(a: Obj, b: Obj) -> Obj {
    Obj::SetFormer(SetFormer::IntervalObj(IntervalObj::LeftOpenRightOpen(
        IntervalObjStruct {
            start: Box::new(a),
            end: Box::new(b),
        },
    )))
}
pub(crate) fn integer_interval(a: Obj, b: Obj) -> Obj {
    Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(a),
        end: Box::new(b),
    }))
}
pub(crate) fn typed(name: crate::ast::names::BoundName, set: Obj) -> TypedParameterGroup {
    TypedParameterGroup {
        params: vec![name],
        param_type: ParamType::Obj(set),
    }
}
pub(crate) fn literal(name: crate::ast::names::BoundName, set: Obj, value: Obj) -> Obj {
    Obj::FunctionSpace(FunctionSpace::AnonymousFn(AnonymousFn {
        body: FnSet {
            set_bound_parameters: SetBoundParameterList {
                groups: vec![SetBoundParameterGroup {
                    params: vec![name],
                    param_type: Box::new(set),
                }],
            },
            dom_facts: vec![],
            ret_set: Box::new(real()),
        },
        equal_to: Box::new(value),
    }))
}
pub(crate) fn function_space(rt: &mut Runtime, start: Obj, end: Obj) -> Obj {
    let name = rt.fresh_internal_param();
    let lower = le(rt, start, id(&name));
    let upper = le(rt, id(&name), end);
    Obj::FunctionSpace(FunctionSpace::FnSet(FnSet {
        set_bound_parameters: SetBoundParameterList {
            groups: vec![SetBoundParameterGroup {
                params: vec![name],
                param_type: Box::new(Obj::StandardSet(StandardSet::Z)),
            }],
        },
        dom_facts: vec![
            QuantifierFreeFact::AtomicFact(lower),
            QuantifierFreeFact::AtomicFact(upper),
        ],
        ret_set: Box::new(real()),
    }))
}
fn fold_closed(value: Obj) -> Obj {
    match crate::rational_expression::evaluate_obj_to_normalized_decimal_number(&value) {
        Some(n) => Obj::Literal(Literal::Number(n)),
        None => value,
    }
}
pub(crate) fn certificate(rt: &mut Runtime, name: &str, body: Vec<Obj>) -> AtomicFact {
    NormalAtomicFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        predicate: AtomicName::plain(name.into()),
        body,
        line_file: None,
    }
    .into()
}
pub(crate) fn member(rt: &mut Runtime, element: Obj, set: Obj) -> AtomicFact {
    InFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        element,
        set,
        line_file: None,
    }
    .into()
}
pub(crate) fn subset(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    SubsetFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(crate) fn eq(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    EqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(crate) fn le(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    LessEqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(crate) fn lt(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    LessFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(crate) fn darboux_sum(rt: &mut Runtime, n: Obj, p: Obj, height: Obj) -> Obj {
    let i = rt.fresh_internal_param();
    let index = id(&i);
    let width = sub(
        analysis_apply(p.clone(), index.clone()),
        analysis_apply(p, sub(index.clone(), num("1"))),
    );
    let summand = mul(analysis_apply(height, index), width);
    let lower = le(rt, num("1"), id(&i));
    let upper = le(rt, id(&i), n.clone());
    let mut function = literal(i, Obj::StandardSet(StandardSet::Z), summand);
    if let Obj::FunctionSpace(FunctionSpace::AnonymousFn(f)) = &mut function {
        f.body.dom_facts = vec![
            QuantifierFreeFact::AtomicFact(lower),
            QuantifierFreeFact::AtomicFact(upper),
        ];
    }
    Obj::IteratedOperator(IteratedOperator::Sum(Sum {
        start: Box::new(num("1")),
        end: Box::new(n),
        func: Box::new(function),
    }))
}
pub(crate) fn oriented_candidate(_rt: &mut Runtime, a: Obj, b: Obj, value: Obj) -> Obj {
    let sign = Obj::ArithmeticOperator(ArithmeticOperator::Sign(Sign {
        arg: Box::new(sub(b, a)),
    }));
    mul(sign, value)
}
