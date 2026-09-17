use super::exec_env::ExecEnv;
use crate::new_pipeline::ast::fact::{AtomicFact, Fact};
use crate::new_pipeline::ast::names::PlainName;
use crate::new_pipeline::parse::keywords::{
    ABSTRACT_PROP, ALGO, AXIOM, PROP, SETTING, STRATEGY, STRUCT, TEMPLATE, THM,
};
use crate::new_pipeline::runtime::{FactId, RuntimeError, RuntimeResult};
use std::collections::HashMap;

// Commit a closed child ExecEnv into `parent`. FactIds are global; only mounts move.
pub fn merge_exec_env_from(parent: &mut ExecEnv, child: &ExecEnv) -> RuntimeResult<()> {
    merge_definitions_from(parent, child)?;
    merge_facts_from(parent, child)?;
    merge_well_defined_objects_from(parent, child)?;
    merge_special_object_properties_from(parent, child);
    merge_prop_rewrite_properties_from(parent, child);
    Ok(())
}

fn merge_definitions_from(parent: &mut ExecEnv, child: &ExecEnv) -> RuntimeResult<()> {
    for (name, info) in child.definitions.identifiers.iter() {
        if parent.definitions.identifiers.contains_key(name) {
            return Err(RuntimeError::InternalBug(format!(
                "merge_exec_env_from: identifier `{name}` already defined in parent"
            )));
        }
        parent
            .definitions
            .identifiers
            .insert(name.clone(), info.clone());
    }
    merge_named_map(
        &mut parent.definitions.predicate_definitions,
        &child.definitions.predicate_definitions,
        PROP,
    )?;
    merge_named_map(
        &mut parent.definitions.abstract_predicate_definitions,
        &child.definitions.abstract_predicate_definitions,
        ABSTRACT_PROP,
    )?;
    merge_named_map(
        &mut parent.definitions.algorithm_definitions,
        &child.definitions.algorithm_definitions,
        ALGO,
    )?;
    merge_named_map(
        &mut parent.definitions.structure_definitions,
        &child.definitions.structure_definitions,
        STRUCT,
    )?;
    merge_named_map(
        &mut parent.definitions.template_definitions,
        &child.definitions.template_definitions,
        TEMPLATE,
    )?;
    merge_named_map(
        &mut parent.definitions.setting_definitions,
        &child.definitions.setting_definitions,
        SETTING,
    )?;
    merge_named_map(
        &mut parent.definitions.theorem_definitions,
        &child.definitions.theorem_definitions,
        THM,
    )?;
    merge_named_map(
        &mut parent.definitions.axiom_definitions,
        &child.definitions.axiom_definitions,
        AXIOM,
    )?;
    merge_named_map(
        &mut parent.definitions.strategy_definitions,
        &child.definitions.strategy_definitions,
        STRATEGY,
    )?;
    Ok(())
}

fn merge_named_map<V: Clone>(
    parent: &mut HashMap<PlainName, V>,
    child: &HashMap<PlainName, V>,
    kind: &str,
) -> RuntimeResult<()> {
    for (name, value) in child.iter() {
        if parent.contains_key(name) {
            return Err(RuntimeError::InternalBug(format!(
                "merge_exec_env_from: {kind} `{name}` already defined in parent"
            )));
        }
        parent.insert(name.clone(), value.clone());
    }
    Ok(())
}

fn merge_facts_from(parent: &mut ExecEnv, child: &ExecEnv) -> RuntimeResult<()> {
    // Replay each child-owned fact once via facts_by_id (global FactId, no realloc).
    let mut fact_ids: Vec<FactId> = child.facts.facts_by_id.keys().copied().collect();
    fact_ids.sort_by_key(|id| id.value());
    for fact_id in fact_ids {
        let fact = child
            .facts
            .facts_by_id
            .get(&fact_id)
            .expect("fact_id from keys");
        if parent.facts.facts_by_id.contains_key(&fact_id) {
            continue;
        }
        match fact {
            Fact::AtomicFact(AtomicFact::EqualFact(equal_fact)) => {
                parent.facts.known_equality.store(equal_fact);
                parent.facts.record_fact(fact_id, fact.clone());
            }
            Fact::AtomicFact(atomic) => {
                index_atomic_except_equality(parent, atomic);
                parent.facts.record_fact(fact_id, fact.clone());
            }
            Fact::OrFact(or_fact) => {
                parent.facts.known_or.store(or_fact);
                parent.facts.record_fact(fact_id, fact.clone());
            }
            _ => {
                parent.facts.record_fact(fact_id, fact.clone());
            }
        }
    }
    // Forall indexes are rebuilt inside record_fact; also merge any orphan
    // index entries is unnecessary when every forall goes through record_fact.
    Ok(())
}

fn index_atomic_except_equality(parent: &mut ExecEnv, atomic_fact: &AtomicFact) {
    let key = atomic_fact.prop_name();
    let positive_polarity =
        crate::new_pipeline::ast::fact::atomic_fact_has_positive_polarity(atomic_fact);
    parent.facts.known_atomic_except_equality_facts.store(
        key,
        positive_polarity,
        atomic_fact.clone(),
    );
}

fn merge_well_defined_objects_from(parent: &mut ExecEnv, child: &ExecEnv) -> RuntimeResult<()> {
    for (object_key, wd_id) in child.well_defined_objects.object_to_wd_id.iter() {
        if let Some(existing) = parent.well_defined_objects.object_to_wd_id.get(object_key) {
            if existing != wd_id {
                return Err(RuntimeError::InternalBug(
                    "merge_exec_env_from: WD object key collides with a different WellDefinednessId"
                        .to_string(),
                ));
            }
            continue;
        }
        parent
            .well_defined_objects
            .object_to_wd_id
            .insert(object_key.clone(), *wd_id);
        if let Some(object) = child.well_defined_objects.wd_id_to_object.get(wd_id) {
            parent
                .well_defined_objects
                .wd_id_to_object
                .insert(*wd_id, object.clone());
        }
    }
    Ok(())
}

fn merge_special_object_properties_from(parent: &mut ExecEnv, child: &ExecEnv) {
    for (key, values) in child.special_object_properties.iter() {
        parent
            .special_object_properties
            .entry(key.clone())
            .or_default()
            .extend(values.iter().cloned());
    }
}

fn merge_prop_rewrite_properties_from(parent: &mut ExecEnv, child: &ExecEnv) {
    for (key, values) in child.prop_rewrite_properties.iter() {
        parent
            .prop_rewrite_properties
            .entry(key.clone())
            .or_default()
            .extend(values.iter().cloned());
    }
}
