use std::collections::HashMap;

use crate::ast::fact::{
    AndChainAtomicFact, AtomicFact, ExistOrAndChainAtomicFact, Fact, ForallFact, NotEqualFact,
    OrFact, PlainExistFact, QuantifierFreeFact,
};
use crate::ast::names::BoundName;
use crate::ast::obj::{IdentifierObj, Obj};
use crate::ast::param::{TypedParameterGroup, TypedParameterList};
use crate::instantiate::quantifier_free_fact_to_fact;
use crate::runtime::Runtime;

// In classical logic, not(exists exactly one x, P(x)) means:
// forall x, P(x) => exists y, P(y) and y != x.
// With several binders, at least one component differs. Carrier dependencies
// are instantiated in source order for the second candidate.
pub(super) fn negate_unique_exist(
    runtime: &mut Runtime,
    plain: &PlainExistFact,
) -> Result<Fact, String> {
    let mut subst = HashMap::new();
    let mut groups = Vec::new();
    let mut different_components = Vec::new();
    for group in &plain.typed_parameters.groups {
        let param_type = runtime
            .inst_param_type(&group.param_type, &subst)
            .map_err(|e| format!("by contra: unique-existence carrier instantiation: {e}"))?;
        let mut params = Vec::new();
        for old in &group.params {
            let fresh = BoundName::new(
                runtime.global_ids.allocate_identifier_id(),
                format!("{}_other{}", old.name, different_components.len()),
            );
            let other = Obj::Identifier(IdentifierObj::from_bound_name(&fresh));
            subst.insert(old.id, other.clone());
            different_components.push(AtomicFact::NotEqualFact(NotEqualFact {
                fact_id: runtime.global_ids.allocate_fact_id(),
                left: other,
                right: Obj::Identifier(IdentifierObj::from_bound_name(old)),
                line_file: plain.line_file.clone(),
            }));
            params.push(fresh);
        }
        groups.push(TypedParameterGroup { params, param_type });
    }
    if different_components.is_empty() {
        return Err("by contra: unique existence needs at least one binder".to_string());
    }
    let mut facts = Vec::new();
    for body in &plain.facts {
        facts.push(
            runtime
                .inst_quantifier_free_fact(body, &subst)
                .map_err(|e| format!("by contra: unique-existence body instantiation: {e}"))?,
        );
    }
    facts.push(if different_components.len() == 1 {
        QuantifierFreeFact::AtomicFact(different_components.remove(0))
    } else {
        QuantifierFreeFact::OrFact(OrFact {
            fact_id: runtime.global_ids.allocate_fact_id(),
            facts: different_components
                .into_iter()
                .map(AndChainAtomicFact::AtomicFact)
                .collect(),
            line_file: plain.line_file.clone(),
        })
    });
    let alternative = PlainExistFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: TypedParameterList { groups },
        facts,
        line_file: plain.line_file.clone(),
    };
    Ok(Fact::ForallFact(ForallFact {
        fact_id: runtime.global_ids.allocate_fact_id(),
        typed_parameters: plain.typed_parameters.clone(),
        dom_facts: plain
            .facts
            .iter()
            .cloned()
            .map(quantifier_free_fact_to_fact)
            .collect(),
        then_facts: vec![ExistOrAndChainAtomicFact::ExistFact(alternative)],
        line_file: plain.line_file.clone(),
    }))
}
