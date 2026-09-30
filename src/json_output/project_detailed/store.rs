//! Store / infer helpers for Detailed projection (`local_env` omitted).

use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::json_output::helper::{object_for, string};
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
    object_for(runtime, entries)
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
    object_for(runtime, vec![
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
    object_for(runtime, vec![
        ("stores", JsonValue::Array(stores)),
        ("infers", JsonValue::Array(Vec::new())),
    ])
}
