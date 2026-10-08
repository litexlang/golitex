use crate::ast::fact::*;
use crate::ast::names::{AtomicName, BoundName};
use crate::ast::obj::*;
use crate::ast::param::*;
use crate::runtime::Runtime;

pub(super) fn number(value: &str) -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: value.to_string(),
    }))
}
pub(super) fn identifier(bound: &BoundName) -> Obj {
    Obj::Identifier(IdentifierObj::from_bound_name(bound))
}
pub(super) fn typed(bound: BoundName, set: Obj) -> TypedParameterList {
    TypedParameterList {
        groups: vec![TypedParameterGroup {
            params: vec![bound],
            param_type: ParamType::Obj(set),
        }],
    }
}
pub(super) fn atomic_in(rt: &mut Runtime, element: Obj, set: Obj) -> AtomicFact {
    InFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        element,
        set,
        line_file: None,
    }
    .into()
}
pub(super) fn equal(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    EqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(super) fn le(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    LessEqualFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(super) fn less(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    LessFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(super) fn subset(rt: &mut Runtime, left: Obj, right: Obj) -> AtomicFact {
    SubsetFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        left,
        right,
        line_file: None,
    }
    .into()
}
pub(super) fn is_set(rt: &mut Runtime, set: Obj) -> AtomicFact {
    IsSetFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        set,
        line_file: None,
    }
    .into()
}
pub(super) fn finite(rt: &mut Runtime, set: Obj) -> AtomicFact {
    IsFiniteSetFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        set,
        line_file: None,
    }
    .into()
}
pub(super) fn nonempty(rt: &mut Runtime, set: Obj) -> AtomicFact {
    IsNonemptySetFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        set,
        line_file: None,
    }
    .into()
}
pub(super) fn certificate(rt: &mut Runtime, name: &str, set: Obj, value: Obj) -> AtomicFact {
    // Legacy completeness certificates are opaque named predicates. Only the
    // reserved completeness theorem introduces them; projection theorems consume them.
    NormalAtomicFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        predicate: AtomicName::plain(name.to_string()),
        body: vec![set, value],
        line_file: None,
    }
    .into()
}
pub(super) fn bijective(rt: &mut Runtime, domain: Obj, codomain: Obj, function: Obj) -> AtomicFact {
    BijectiveFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        domain,
        codomain,
        function,
        line_file: None,
    }
    .into()
}
pub(super) fn forall(
    rt: &mut Runtime,
    bound: BoundName,
    set: Obj,
    dom: Vec<Fact>,
    body: Vec<AtomicFact>,
) -> Fact {
    Fact::ForallFact(ForallFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        typed_parameters: typed(bound, set),
        dom_facts: dom,
        then_facts: body
            .into_iter()
            .map(ExistOrAndChainAtomicFact::AtomicFact)
            .collect(),
        line_file: None,
    })
}
pub(super) fn exist(
    rt: &mut Runtime,
    params: TypedParameterList,
    body: Vec<AtomicFact>,
    unique: bool,
) -> Fact {
    let facts = if body.len() > 1 && !unique {
        vec![QuantifierFreeFact::AndFact(AndFact {
            fact_id: rt.global_ids.allocate_fact_id(),
            facts: body,
            line_file: None,
        })]
    } else {
        body.into_iter()
            .map(QuantifierFreeFact::AtomicFact)
            .collect()
    };
    let body = PlainExistFact {
        fact_id: rt.global_ids.allocate_fact_id(),
        typed_parameters: params,
        facts,
        line_file: None,
    };
    if unique {
        Fact::ExistUniqueFact(body)
    } else {
        Fact::ExistFact(body)
    }
}
pub(super) fn range(start: Obj, end: Obj) -> Obj {
    Obj::SetFormer(SetFormer::ClosedRange(ClosedRange {
        start: Box::new(start),
        end: Box::new(end),
    }))
}
pub(super) fn size(set: Obj) -> Obj {
    Obj::FiniteSetStat(FiniteSetStat::FiniteSetSize(FiniteSetSize {
        set: Box::new(set),
    }))
}
pub(super) fn apply(function: &Obj, args: Vec<Obj>) -> Result<Obj, String> {
    let head = match function {
        Obj::Identifier(x) => FnObjHead::Identifier(x.clone()),
        Obj::FunctionSpace(FunctionSpace::AnonymousFn(x)) => {
            FnObjHead::AnonymousFnLiteral(Box::new(x.clone()))
        }
        Obj::StructAndFieldAccessObj(StructAndFieldAccessObj::FieldAccess(x)) => {
            FnObjHead::FieldAccess(x.clone())
        }
        Obj::InstantiatedTemplateObj(x) => FnObjHead::InstantiatedTemplateObj(x.clone()),
        _ => return Err("expected a callable function object".to_string()),
    };
    Ok(Obj::FnObj(FnObj {
        head: Box::new(head),
        body: vec![args.into_iter().map(Box::new).collect()],
    }))
}
pub(super) fn unary_fn(rt: &mut Runtime, domain: Obj, codomain: Obj) -> Obj {
    let param = rt.fresh_internal_param();
    Obj::FunctionSpace(FunctionSpace::FnSet(FnSet {
        set_bound_parameters: SetBoundParameterList {
            groups: vec![SetBoundParameterGroup {
                params: vec![param],
                param_type: Box::new(domain),
            }],
        },
        dom_facts: vec![],
        ret_set: Box::new(codomain),
    }))
}
