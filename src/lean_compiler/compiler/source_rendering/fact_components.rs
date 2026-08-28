//! Typed extraction and validation of fact and object components.

use super::super::*;

pub(in super::super) fn membership_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::InFact(fact)) => Ok((&fact.element, &fact.set)),
        _ => Err(format!("expected membership fact, found `{fact}`")),
    }
}

pub(in super::super) fn subset_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::SubsetFact(fact)) => Ok((&fact.left, &fact.right)),
        Fact::AtomicFact(AtomicFact::SupersetFact(fact)) => Ok((&fact.right, &fact.left)),
        _ => Err(format!("expected subset fact, found `{fact}`")),
    }
}

pub(in super::super) fn validate_forall_fact_as_subset(
    candidate: &Fact,
    expected_subset: &Fact,
) -> Result<(), String> {
    let Fact::ForallFact(candidate) = candidate else {
        return Err("child is neither the expected subset nor a forall spelling".into());
    };
    let (expected_source, expected_target) = subset_parts(expected_subset)?;
    let parameters = candidate
        .typed_parameters
        .collect_param_bindings_with_types();
    let [parameter] = parameters.as_slice() else {
        return Err("subset forall must retain exactly one parameter".into());
    };
    let ParamType::Obj(ref parameter_set) = parameter.1 else {
        return Err("subset forall parameter has no object-set type".into());
    };
    if obj_equality_key(parameter_set) != obj_equality_key(expected_source)
        || !candidate.dom_facts.is_empty()
        || candidate.then_facts.len() != 1
    {
        return Err("subset forall changed its source, domains, or conclusion arity".into());
    }
    let conclusion = candidate.then_facts[0].clone().to_fact();
    let (element, target_set) = membership_parts(&conclusion)?;
    let expected_element = obj_for_bound_param_in_scope(&parameter.0);
    if obj_equality_key(element) != obj_equality_key(&expected_element)
        || obj_equality_key(target_set) != obj_equality_key(expected_target)
    {
        return Err("subset forall changed its bound element or target set".into());
    }
    Ok(())
}

/// Returns the semantic subset orientation `(source, target)`, whether the
/// relation is negated, and whether the source used subset rather than
/// superset spelling.
pub(in super::super) fn normalized_set_relation_parts(
    fact: &Fact,
) -> Result<(&Obj, &Obj, bool, bool), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::SubsetFact(fact)) => {
            Ok((&fact.left, &fact.right, false, true))
        }
        Fact::AtomicFact(AtomicFact::SupersetFact(fact)) => {
            Ok((&fact.right, &fact.left, false, false))
        }
        Fact::AtomicFact(AtomicFact::NotSubsetFact(fact)) => {
            Ok((&fact.left, &fact.right, true, true))
        }
        Fact::AtomicFact(AtomicFact::NotSupersetFact(fact)) => {
            Ok((&fact.right, &fact.left, true, false))
        }
        _ => Err(format!("expected a set relation, found `{fact}`")),
    }
}

pub(in super::super) fn finite_set_parts(fact: &Fact) -> Result<&Obj, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::IsFiniteSetFact(fact)) => Ok(&fact.set),
        _ => Err(format!("expected finite-set fact, found `{fact}`")),
    }
}

pub(in super::super) fn nonempty_set_parts(fact: &Fact) -> Result<&Obj, String> {
    match fact {
        Fact::AtomicFact(AtomicFact::IsNonemptySetFact(fact)) => Ok(&fact.set),
        _ => Err(format!("expected nonempty-set fact, found `{fact}`")),
    }
}

pub(in super::super) fn nonmembership_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NotInFact(fact)) => Ok((&fact.element, &fact.set)),
        _ => Err(format!("expected non-membership fact, found `{fact}`")),
    }
}

pub(in super::super) fn equality_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::EqualFact(fact)) => Ok((&fact.left, &fact.right)),
        _ => Err(format!("expected equality fact, found `{fact}`")),
    }
}

pub(in super::super) fn not_equal_parts(fact: &Fact) -> Result<(&Obj, &Obj), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::NotEqualFact(fact)) => Ok((&fact.left, &fact.right)),
        _ => Err(format!("expected not-equality fact, found `{fact}`")),
    }
}

pub(in super::super) fn positive_order_parts(
    fact: &Fact,
    strict: bool,
) -> Result<(&Obj, &Obj), String> {
    match (strict, fact) {
        (true, Fact::AtomicFact(AtomicFact::LessFact(fact))) => Ok((&fact.left, &fact.right)),
        (true, Fact::AtomicFact(AtomicFact::GreaterFact(fact))) => Ok((&fact.right, &fact.left)),
        (false, Fact::AtomicFact(AtomicFact::LessEqualFact(fact))) => Ok((&fact.left, &fact.right)),
        (false, Fact::AtomicFact(AtomicFact::GreaterEqualFact(fact))) => {
            Ok((&fact.right, &fact.left))
        }
        (true, _) => Err(format!(
            "expected strict positive-order fact, found `{fact}`"
        )),
        (false, _) => Err(format!(
            "expected non-strict positive-order fact, found `{fact}`"
        )),
    }
}

pub(in super::super) fn order_relation_parts(fact: &Fact) -> Result<(&Obj, &Obj, bool), String> {
    match fact {
        Fact::AtomicFact(AtomicFact::LessFact(fact)) => Ok((&fact.left, &fact.right, true)),
        Fact::AtomicFact(AtomicFact::GreaterFact(fact)) => Ok((&fact.right, &fact.left, true)),
        Fact::AtomicFact(AtomicFact::LessEqualFact(fact)) => Ok((&fact.left, &fact.right, false)),
        Fact::AtomicFact(AtomicFact::GreaterEqualFact(fact)) => {
            Ok((&fact.right, &fact.left, false))
        }
        _ => Err(format!(
            "expected positive ordered relation, found `{fact}`"
        )),
    }
}

pub(in super::super) fn is_literal_zero(object: &Obj) -> bool {
    matches!(object, Obj::Number(number) if number.normalized_value == "0")
}

pub(in super::super) fn addition_parts(object: &Obj) -> Result<(&Obj, &Obj), String> {
    let Obj::Add(addition) = object else {
        return Err(format!("expected an addition object, found `{object}`"));
    };
    Ok((addition.left.as_ref(), addition.right.as_ref()))
}
