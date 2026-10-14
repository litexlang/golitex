use crate::ast::fact::{AndChainAtomicFact, EqualFact, Fact, ForallFact, InFact, OrFact};
use crate::ast::line_file::SourceLine;
use crate::ast::obj::{ClosedRange, ListSet, Literal, Number, Obj, Range, SetFormer};
use crate::ast::param::ParamType;
use crate::ast::stmt::ClosedRangeOrRange;
use crate::rational_expression::exact_rational::evaluate_obj_to_exact_rational_for_eval;
use crate::runtime::runtime_ids::IdentifierId;
use crate::runtime::Runtime;
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
    let end =
        obj_to_i128(&range.end).ok_or_else(|| "range end is not a concrete integer".to_string())?;
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

// Soft work limit for `by enumerate finite_set` / `by for` assignment products.
// Checked before any assignment map is built; overflow is treated as over-budget.
pub(super) const MAX_ENUMERATION_ASSIGNMENTS: usize = 1024;

pub(super) fn enumeration_assignment_count(
    domains: &[(IdentifierId, String, Vec<Obj>)],
) -> Result<usize, String> {
    let mut total: usize = 1;
    for (_id, _name, values) in domains {
        if values.is_empty() {
            return Ok(0);
        }
        match total.checked_mul(values.len()) {
            Some(next) if next <= MAX_ENUMERATION_ASSIGNMENTS => total = next,
            Some(next) => {
                return Err(format!(
                    "finite enumeration product has {next} assignments, which exceeds the assignment budget of {MAX_ENUMERATION_ASSIGNMENTS}"
                ));
            }
            None => {
                return Err(format!(
                    "finite enumeration product exceeds the assignment budget of {MAX_ENUMERATION_ASSIGNMENTS}"
                ));
            }
        }
    }
    Ok(total)
}

// Yields one assignment at a time in the same order as the old eager Cartesian
// product (last binder varies fastest). Example: domains a:{0,1}, b:{2,3}
// give (a=0,b=2), (a=0,b=3), (a=1,b=2), (a=1,b=3).
pub(super) struct CartesianAssignments<'a> {
    domains: &'a [(IdentifierId, String, Vec<Obj>)],
    index: usize,
    total: usize,
}

impl<'a> CartesianAssignments<'a> {
    pub(super) fn new(domains: &'a [(IdentifierId, String, Vec<Obj>)]) -> Result<Self, String> {
        let total = enumeration_assignment_count(domains)?;
        Ok(Self {
            domains,
            index: 0,
            total,
        })
    }

    pub(super) fn len(&self) -> usize {
        self.total
    }
}

impl Iterator for CartesianAssignments<'_> {
    type Item = HashMap<IdentifierId, Obj>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.total {
            return None;
        }
        let subst = assignment_at(self.domains, self.index);
        self.index += 1;
        Some(subst)
    }
}

fn assignment_at(
    domains: &[(IdentifierId, String, Vec<Obj>)],
    index: usize,
) -> HashMap<IdentifierId, Obj> {
    let mut remaining = index;
    let mut subst = HashMap::new();
    for (id, _name, values) in domains.iter().rev() {
        let n = values.len();
        let choice = remaining % n;
        remaining /= n;
        subst.insert(*id, values[choice].clone());
    }
    subst
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

#[cfg(test)]
mod tests {
    use super::*;

    fn binary_domains(binder_count: usize) -> Vec<(IdentifierId, String, Vec<Obj>)> {
        let values = vec![number_obj(0), number_obj(1)];
        (0..binder_count)
            .map(|i| (IdentifierId::new(i as u64), format!("b{i}"), values.clone()))
            .collect()
    }

    #[test]
    fn lazy_cartesian_matches_two_by_two_order() {
        let domains = vec![
            (
                IdentifierId::new(1),
                "a".to_string(),
                vec![number_obj(0), number_obj(1)],
            ),
            (
                IdentifierId::new(2),
                "b".to_string(),
                vec![number_obj(2), number_obj(3)],
            ),
        ];
        let got: Vec<_> = CartesianAssignments::new(&domains)
            .expect("within budget")
            .map(|m| {
                (
                    obj_to_i128(m.get(&IdentifierId::new(1)).unwrap()).unwrap(),
                    obj_to_i128(m.get(&IdentifierId::new(2)).unwrap()).unwrap(),
                )
            })
            .collect();
        assert_eq!(got, vec![(0, 2), (0, 3), (1, 2), (1, 3)]);
    }

    #[test]
    fn over_budget_product_rejects_without_building_assignments() {
        // 2^20 exceeds the budget; the count check must fail before any map is built.
        let domains = binary_domains(20);
        let err = enumeration_assignment_count(&domains).expect_err("over budget");
        assert!(err.contains("exceeds the assignment budget"));
        assert!(CartesianAssignments::new(&domains).is_err());
    }

    #[test]
    fn empty_factor_yields_zero_assignments() {
        let domains = vec![
            (IdentifierId::new(1), "a".to_string(), vec![number_obj(0)]),
            (IdentifierId::new(2), "b".to_string(), Vec::new()),
        ];
        assert_eq!(enumeration_assignment_count(&domains).unwrap(), 0);
        assert_eq!(CartesianAssignments::new(&domains).unwrap().count(), 0);
    }
}
