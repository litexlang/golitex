//! Store / infer / local_env helpers for Detailed projection.

use crate::exec_env::exec_env::ExecEnv;
use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::json_output::helper::{object, string};
use crate::knowledge_base::JsonValue;
use crate::runtime::{FactId, Runtime};
use crate::store_fact_and_infer::StoreFactAndInferResult;

pub(super) fn project_verify_facts(facts: &[VerifyFactResult], runtime: &Runtime) -> JsonValue {
    JsonValue::Array(
        facts
            .iter()
            .map(|f| super::verify::project_verify_fact(f, runtime))
            .collect(),
    )
}

pub(super) fn fact_id_entry(runtime: &Runtime, fact_id: FactId) -> JsonValue {
    let mut entries = vec![("fact_id", string(fact_id.to_string()))];
    if let Some(fact) = runtime.fact_by_id_in_stack(fact_id) {
        entries.push(("fact", string(fact.readable_string())));
    }
    object(entries)
}

// Detailed store/infer: keep fact_id + readable text. No search_trace (T1).
pub(super) fn project_store_and_infer(
    node: &StoreFactAndInferResult,
    runtime: &Runtime,
) -> JsonValue {
    let store_ids = node.store.stored_fact_ids();
    let all_ids = node.stored_fact_ids();
    let stores: Vec<JsonValue> = store_ids
        .iter()
        .copied()
        .map(|id| fact_id_entry(runtime, id))
        .collect();
    let infers: Vec<JsonValue> = all_ids
        .into_iter()
        .filter(|id| !store_ids.contains(id))
        .map(|id| fact_id_entry(runtime, id))
        .collect();
    object(vec![
        ("stores", JsonValue::Array(stores)),
        ("infers", JsonValue::Array(infers)),
    ])
}

pub(super) fn project_have_store_ids(fact_ids: &[FactId], runtime: &Runtime) -> JsonValue {
    let stores: Vec<JsonValue> = fact_ids
        .iter()
        .copied()
        .map(|id| fact_id_entry(runtime, id))
        .collect();
    object(vec![
        ("stores", JsonValue::Array(stores)),
        ("infers", JsonValue::Array(Vec::new())),
    ])
}

// L2: binder-scope summary only (identifiers + facts in this env), not full ExecEnv dump.
pub(super) fn project_local_env_summary(env: &ExecEnv, _runtime: &Runtime) -> JsonValue {
    let mut identifiers: Vec<String> = env
        .definitions
        .identifiers
        .keys()
        .map(|k| k.clone())
        .collect();
    identifiers.sort();

    let mut fact_ids: Vec<FactId> = env.facts.facts_by_id.keys().copied().collect();
    fact_ids.sort_by_key(|id| id.value());
    let facts: Vec<JsonValue> = fact_ids
        .into_iter()
        .map(|id| {
            let mut entries = vec![("fact_id", string(id.to_string()))];
            if let Some(fact) = env.facts.facts_by_id.get(&id) {
                entries.push(("fact", string(fact.readable_string())));
            }
            object(entries)
        })
        .collect();

    let mut wd_ids: Vec<_> = env
        .well_defined_objects
        .wd_id_to_object
        .keys()
        .copied()
        .collect();
    wd_ids.sort_by_key(|id| id.value());
    let well_defined: Vec<JsonValue> = wd_ids
        .into_iter()
        .map(|id| {
            let mut entries = vec![("wd_id", string(id.to_string()))];
            if let Some(obj) = env.well_defined_objects.wd_id_to_object.get(&id) {
                entries.push(("obj", string(obj.readable_string())));
            }
            object(entries)
        })
        .collect();

    object(vec![
        (
            "identifiers",
            JsonValue::Array(identifiers.into_iter().map(string).collect()),
        ),
        ("facts", JsonValue::Array(facts)),
        ("well_defined", JsonValue::Array(well_defined)),
    ])
}
