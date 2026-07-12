use crate::common::json_value::JsonValue;
use crate::prelude::{Fact, InferResult, StoreFactOutput};

use super::fields::user_visible_stmt_or_msg_text;

pub(crate) fn store_fact_json_values(infers: &InferResult) -> Vec<JsonValue> {
    infers
        .store_fact_outputs()
        .iter()
        .map(store_fact_json_value)
        .collect::<Vec<_>>()
}

fn store_fact_json_value(output: &StoreFactOutput) -> JsonValue {
    let fact = &output.itself_and_why_itself_is_stored.0;
    let reason = &output.itself_and_why_itself_is_stored.1;
    let inferred_fact_items = unique_fact_strings(&output.inferred_facts)
        .into_iter()
        .map(JsonValue::JsonString)
        .collect::<Vec<_>>();

    JsonValue::Object(vec![
        (
            "fact".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&fact.to_string())),
        ),
        ("reason".to_string(), JsonValue::JsonString(reason.clone())),
        (
            "inferred_facts".to_string(),
            JsonValue::Array(inferred_fact_items),
        ),
    ])
}

fn unique_fact_strings(facts: &[Fact]) -> Vec<String> {
    let mut out = Vec::new();
    for fact in facts {
        let text = user_visible_stmt_or_msg_text(&fact.to_string());
        if !out.contains(&text) {
            out.push(text);
        }
    }
    out
}
