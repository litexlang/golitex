use crate::compile_to_lean::helper::{instantiated_fact_matches, instantiated_object_matches};
use crate::prelude::*;
use std::collections::{HashMap, HashSet};

/// Construct the one/two-binder result of the checked real-line certificate.
pub(super) fn real_comparison_witness(
    base: &str,
    membership: &str,
    relation: &str,
    witness_left: bool,
    two_parameters: bool,
) -> String {
    let mut steps = vec![
        format!("let _real_base := {base}"),
        format!("have _real_base_member : Litex.In _real_base Litex.R := {membership}"),
    ];
    let (witness, member, proof) = if relation == "eq" {
        ("_real_base", "_real_base_member", "(by rfl)".to_string())
    } else {
        let lemma = if witness_left {
            "existsRealBelow"
        } else {
            "existsRealAbove"
        };
        steps.push(format!("obtain ⟨_real_witness, _real_member, _real_order⟩ := Litex.{lemma} _real_base _real_base_member"));
        let arguments = if witness_left {
            "_real_witness _real_base"
        } else {
            "_real_base _real_witness"
        };
        let proof = match relation {
            "ne" => format!("(Litex.ltNotSame {arguments} _real_order)"),
            "le" => format!("(Litex.ltToLe {arguments} _real_order)"),
            _ => "_real_order".to_string(),
        };
        ("_real_witness", "_real_member", proof)
    };
    let prefix = if two_parameters {
        "_real_base, _real_base_member, "
    } else {
        ""
    };
    steps.push(format!("exact ⟨{prefix}{witness}, {member}, {proof}⟩"));
    format!("(by\n  {})", steps.join("\n  "))
}

/// Check the complete instantiated existential, including binders' carriers.
/// This compares original captures; it allocates no source identities.
pub(super) fn exist_instance_matches(
    source: &PlainExistFact,
    goal: &PlainExistFact,
    substitution: &HashMap<IdentifierId, Obj>,
) -> bool {
    if source.typed_parameters.groups.len() != goal.typed_parameters.groups.len()
        || source.facts.len() != goal.facts.len()
    {
        return false;
    }
    let mut scoped = substitution.clone();
    let mut local_ids = HashSet::new();
    let mut goal_ids = HashSet::new();
    for (old, new) in source
        .typed_parameters
        .groups
        .iter()
        .zip(&goal.typed_parameters.groups)
    {
        if old.params.len() != new.params.len()
            || !match (&old.param_type, &new.param_type) {
                (ParamType::Obj(a), ParamType::Obj(b)) => {
                    instantiated_object_matches(a, b, &scoped)
                }
                (ParamType::Set(_), ParamType::Set(_)) => true,
                _ => false,
            }
        {
            return false;
        }
        for (old, new) in old.params.iter().zip(&new.params) {
            if substitution.contains_key(&old.id)
                || !local_ids.insert(old.id)
                || !goal_ids.insert(new.id)
            {
                return false;
            }
            scoped.insert(old.id, Obj::Identifier(IdentifierObj::from_bound_name(new)));
        }
    }
    source.facts.iter().zip(&goal.facts).all(|(a, b)| {
        instantiated_fact_matches(
            &crate::instantiate::quantifier_free_fact_to_fact(a.clone()),
            &crate::instantiate::quantifier_free_fact_to_fact(b.clone()),
            &scoped,
        )
    })
}
