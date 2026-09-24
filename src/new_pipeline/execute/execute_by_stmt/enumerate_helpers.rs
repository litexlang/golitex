use crate::new_pipeline::ast::fact::{
    AndChainAtomicFact, EqualFact, Fact, ForallFact, InFact, OrFact,
};
use crate::new_pipeline::ast::line_file::SourceLine;
use crate::new_pipeline::ast::obj::{ClosedRange, IdentifierObj, ListSet, Number, Obj, Range, Literal, SetFormer};
use crate::new_pipeline::ast::param::ParamType;
use crate::new_pipeline::ast::stmt::ClosedRangeOrRange;
use crate::new_pipeline::rational_expression::exact_rational::evaluate_obj_to_exact_rational_for_eval;
use crate::new_pipeline::runtime::runtime_ids::IdentifierId;
use crate::new_pipeline::runtime::Runtime;
use std::collections::HashMap;

pub(super) fn obj_to_i128(obj: &Obj) -> Option<i128> {
    let rational = evaluate_obj_to_exact_rational_for_eval(obj)?;
    rational.to_i128_if_integer()
}

pub(super) fn number_obj(n: i128) -> Obj {
    Obj::Literal(Literal::Number(Number {
        normalized_value: n.to_string(),
    }))
}

pub(super) fn expand_closed_range_values(range: &ClosedRange) -> Result<Vec<Obj>, String> {
    let start = obj_to_i128(&range.start)
        .ok_or_else(|| "closed_range start is not a concrete integer".to_string())?;
    let end = obj_to_i128(&range.end)
        .ok_or_else(|| "closed_range end is not a concrete integer".to_string())?;
    if end < start {
        return Ok(Vec::new());
    }
    Ok((start..=end).map(number_obj).collect())
}

pub(super) fn expand_range_values(range: &Range) -> Result<Vec<Obj>, String> {
    let start = obj_to_i128(&range.start)
        .ok_or_else(|| "range start is not a concrete integer".to_string())?;
    let end = obj_to_i128(&range.end)
        .ok_or_else(|| "range end is not a concrete integer".to_string())?;
    if end <= start {
        return Ok(Vec::new());
    }
    Ok((start..end).map(number_obj).collect())
}

pub(super) fn expand_closed_range_or_range(range: &ClosedRangeOrRange) -> Result<Vec<Obj>, String> {
    match range {
        ClosedRangeOrRange::ClosedRange(r) => expand_closed_range_values(r),
        ClosedRangeOrRange::Range(r) => expand_range_values(r),
    }
}

pub(super) fn resolve_param_domain_values(param_type: &ParamType) -> Result<Vec<Obj>, String> {
    match param_type {
        ParamType::Obj(Obj::SetFormer(SetFormer::ListSet(ListSet { list }))) => {
            Ok(list.iter().map(|x| (**x).clone()).collect())
        }
        ParamType::Obj(Obj::SetFormer(SetFormer::ClosedRange(r))) => expand_closed_range_values(r),
        ParamType::Obj(Obj::SetFormer(SetFormer::Range(r))) => expand_range_values(r),
        ParamType::Obj(_) => Err(
            "parameter domain must be a displayed finite list set, range, or closed_range"
                .to_string(),
        ),
        _ => Err("parameter type must be an object domain for enumeration".to_string()),
    }
}

pub(super) fn forall_param_domains(
    forall: &ForallFact,
) -> Result<Vec<(IdentifierId, String, Vec<Obj>)>, String> {
    let mut out = Vec::new();
    for group in &forall.typed_parameters.groups {
        let values = resolve_param_domain_values(&group.param_type)?;
        for param in &group.params {
            out.push((param.id, param.name.clone(), values.clone()));
        }
    }
    if out.is_empty() {
        return Err("forall has no parameters to enumerate".to_string());
    }
    Ok(out)
}

pub(super) fn cartesian_assignments(
    domains: &[(IdentifierId, String, Vec<Obj>)],
) -> Vec<HashMap<IdentifierId, Obj>> {
    let mut acc = vec![HashMap::new()];
    for (id, _name, values) in domains {
        let mut next = Vec::new();
        for prefix in &acc {
            for value in values {
                let mut m = prefix.clone();
                m.insert(*id, value.clone());
                next.push(m);
            }
        }
        acc = next;
        if acc.is_empty() {
            break;
        }
    }
    acc
}

pub(super) fn membership_or_equalities_fact(
    runtime: &mut Runtime,
    element: &Obj,
    values: &[Obj],
    line_file: &SourceLine,
) -> Fact {
    let branches: Vec<AndChainAtomicFact> = values
        .iter()
        .map(|v| {
            AndChainAtomicFact::AtomicFact(
                EqualFact {
                    fact_id: runtime.global_ids.allocate_fact_id(),
                    left: element.clone(),
                    right: v.clone(),
                    line_file: Some(line_file.clone()),
                }
                .into(),
            )
        })
        .collect();
    Fact::OrFact(OrFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        facts: branches,
        line_file: Some(line_file.clone()),
    })
}

pub(super) fn closed_range_or_range_as_obj(range: &ClosedRangeOrRange) -> Obj {
    match range {
        ClosedRangeOrRange::ClosedRange(r) => Obj::SetFormer(SetFormer::ClosedRange(r.clone())),
        ClosedRangeOrRange::Range(r) => Obj::SetFormer(SetFormer::Range(r.clone())),
    }
}

// `x $in range(a, b)` / `x $in closed_range(a, b)` used as the membership guard
// before storing the expanded equality cases.
pub(super) fn membership_in_fact(
    runtime: &mut Runtime,
    element: &Obj,
    set: Obj,
    line_file: &SourceLine,
) -> Fact {
    Fact::AtomicFact(
        InFact {
            fact_id: runtime.global_ids.allocate_fact_id(),
            element: element.clone(),
            set,
            line_file: Some(line_file.clone()),
        }
        .into(),
    )
}

pub(super) fn identifier_obj(id: IdentifierId, name: String) -> Obj {
    Obj::Identifier(IdentifierObj::plain(id, name))
}
