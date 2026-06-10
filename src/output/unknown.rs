use crate::common::json_value::JsonValue;
use crate::prelude::*;

use super::fields::user_visible_stmt_or_msg_text;
use super::normalize::json_value_is_empty_in_normal_output;

pub(crate) fn unknown_result_json_value(
    runtime: &Runtime,
    unknown_result: &RuntimeErrorUnknownResult,
) -> JsonValue {
    match unknown_result {
        RuntimeErrorUnknownResult::Generic(unknown) => generic_unknown_json_value(runtime, unknown),
        RuntimeErrorUnknownResult::Fact(unknown) => {
            fact_unknown_json_value(runtime, unknown.as_ref())
        }
    }
}

fn generic_unknown_json_value(runtime: &Runtime, unknown: &StmtUnknown) -> JsonValue {
    let mut fields = vec![(
        "type".to_string(),
        JsonValue::JsonString("unknown".to_string()),
    )];
    push_detail_field(runtime, &mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn fact_unknown_json_value(runtime: &Runtime, unknown: &FactUnknown) -> JsonValue {
    match unknown {
        FactUnknown::AtomicFact(x) => atomic_fact_unknown_json_value(runtime, x),
        FactUnknown::ExistFact(x) => exist_fact_unknown_json_value(runtime, x),
        FactUnknown::OrFact(x) => or_fact_unknown_json_value(runtime, x),
        FactUnknown::AndFact(x) => and_fact_unknown_json_value(runtime, x),
        FactUnknown::ChainFact(x) => chain_fact_unknown_json_value(runtime, x),
        FactUnknown::ForallFact(x) => forall_fact_unknown_json_value(runtime, x),
        FactUnknown::ForallFactWithIff(x) => forall_iff_unknown_json_value(runtime, x),
        FactUnknown::NotForall(x) => not_forall_unknown_json_value(runtime, x),
    }
}

fn atomic_fact_unknown_json_value(runtime: &Runtime, unknown: &AtomicFactUnknown) -> JsonValue {
    let mut fields = base_fact_unknown_fields("atomic fact unknown", &unknown.goal);
    push_detail_field(runtime, &mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn exist_fact_unknown_json_value(runtime: &Runtime, unknown: &ExistFactUnknown) -> JsonValue {
    let mut fields = base_fact_unknown_fields("exist fact unknown", &unknown.goal);
    push_json_field(
        runtime,
        &mut fields,
        "witness_params",
        JsonValue::Array(param_items(&unknown.witness_params)),
    );
    push_json_field(
        runtime,
        &mut fields,
        "body",
        JsonValue::Array(fact_items(&unknown.body)),
    );
    push_detail_field(runtime, &mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn or_fact_unknown_json_value(runtime: &Runtime, unknown: &OrFactUnknown) -> JsonValue {
    let mut fields = base_fact_unknown_fields("or fact unknown", &unknown.goal);
    push_json_field(
        runtime,
        &mut fields,
        "branches",
        JsonValue::Array(fact_items(&unknown.branches)),
    );
    push_detail_field(runtime, &mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn and_fact_unknown_json_value(runtime: &Runtime, unknown: &AndFactUnknown) -> JsonValue {
    let mut fields = base_fact_unknown_fields("and fact unknown", &unknown.goal);
    push_part_field(
        runtime,
        &mut fields,
        "failed_part",
        unknown.failed_part.as_ref(),
    );
    push_detail_field(runtime, &mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn chain_fact_unknown_json_value(runtime: &Runtime, unknown: &ChainFactUnknown) -> JsonValue {
    let mut fields = base_fact_unknown_fields("chain fact unknown", &unknown.goal);
    push_part_field(
        runtime,
        &mut fields,
        "failed_chain_step",
        unknown.failed_part.as_ref(),
    );
    push_detail_field(runtime, &mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn forall_fact_unknown_json_value(runtime: &Runtime, unknown: &ForallFactUnknown) -> JsonValue {
    let mut fields = base_fact_unknown_fields("forall unknown", &unknown.goal);
    push_json_field(
        runtime,
        &mut fields,
        "params",
        JsonValue::Array(param_items(&unknown.params)),
    );
    push_json_field(
        runtime,
        &mut fields,
        "requirements",
        JsonValue::Array(fact_items(&unknown.requirements)),
    );
    push_part_field(
        runtime,
        &mut fields,
        "failed_prove",
        unknown.failed_prove.as_ref(),
    );
    push_detail_field(runtime, &mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn forall_iff_unknown_json_value(
    runtime: &Runtime,
    unknown: &ForallFactWithIffUnknown,
) -> JsonValue {
    let mut fields = base_fact_unknown_fields("forall iff unknown", &unknown.goal);
    push_json_field(
        runtime,
        &mut fields,
        "params",
        JsonValue::Array(param_items(&unknown.params)),
    );
    push_json_field(
        runtime,
        &mut fields,
        "requirements",
        JsonValue::Array(fact_items(&unknown.requirements)),
    );
    if let Some(direction) = &unknown.failed_direction {
        fields.push((
            "failed_direction".to_string(),
            JsonValue::JsonString(direction.clone()),
        ));
    }
    if let Some(child_unknown) = &unknown.child_unknown {
        fields.push((
            "unknown_result".to_string(),
            fact_unknown_json_value(runtime, child_unknown.as_ref()),
        ));
    }
    push_detail_field(runtime, &mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn not_forall_unknown_json_value(runtime: &Runtime, unknown: &NotForallUnknown) -> JsonValue {
    let mut fields = base_fact_unknown_fields("not forall unknown", &unknown.goal);
    push_detail_field(runtime, &mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn base_fact_unknown_fields(label: &str, goal: &Fact) -> Vec<(String, JsonValue)> {
    vec![
        ("type".to_string(), JsonValue::JsonString(label.to_string())),
        (
            "goal".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&goal.to_string())),
        ),
    ]
}

fn push_part_field(
    runtime: &Runtime,
    fields: &mut Vec<(String, JsonValue)>,
    key: &str,
    part: Option<&FactUnknownPart>,
) {
    if let Some(part) = part {
        fields.push((key.to_string(), part_json_value(runtime, part)));
    } else if runtime.detail_output {
        fields.push((key.to_string(), JsonValue::Object(vec![])));
    }
}

fn part_json_value(runtime: &Runtime, part: &FactUnknownPart) -> JsonValue {
    let mut fields = Vec::new();
    if runtime.detail_output {
        fields.push(("index".to_string(), JsonValue::Number(part.index)));
        fields.push(("count".to_string(), JsonValue::Number(part.count)));
    }
    fields.push((
        "stmt".to_string(),
        JsonValue::JsonString(user_visible_stmt_or_msg_text(&part.stmt.to_string())),
    ));
    if let Some(unknown) = &part.unknown {
        if should_show_nested_part_unknown(runtime, part, unknown.as_ref()) {
            fields.push((
                "unknown_result".to_string(),
                fact_unknown_json_value(runtime, unknown.as_ref()),
            ));
        }
    }
    JsonValue::Object(fields)
}

fn should_show_nested_part_unknown(
    runtime: &Runtime,
    part: &FactUnknownPart,
    unknown: &FactUnknown,
) -> bool {
    if runtime.detail_output {
        return true;
    }
    !is_trivial_atomic_unknown_for_same_fact(part, unknown)
}

fn is_trivial_atomic_unknown_for_same_fact(part: &FactUnknownPart, unknown: &FactUnknown) -> bool {
    let FactUnknown::AtomicFact(atomic_unknown) = unknown else {
        return false;
    };
    atomic_unknown.detail.is_none() && atomic_unknown.goal.to_string() == part.stmt.to_string()
}

fn push_detail_field(
    runtime: &Runtime,
    fields: &mut Vec<(String, JsonValue)>,
    detail: Option<&[String]>,
) {
    let detail_items = detail
        .unwrap_or(&[])
        .iter()
        .map(|line| JsonValue::JsonString(user_visible_stmt_or_msg_text(line)))
        .collect::<Vec<_>>();
    push_json_field(runtime, fields, "detail", JsonValue::Array(detail_items));
}

fn push_json_field(
    runtime: &Runtime,
    fields: &mut Vec<(String, JsonValue)>,
    key: &str,
    value: JsonValue,
) {
    if runtime.detail_output || !json_value_is_empty_in_normal_output(&value) {
        fields.push((key.to_string(), value));
    }
}

fn param_items(params: &[FactUnknownParam]) -> Vec<JsonValue> {
    params
        .iter()
        .map(|param| {
            JsonValue::Object(vec![
                (
                    "name".to_string(),
                    JsonValue::JsonString(user_visible_stmt_or_msg_text(&param.name)),
                ),
                (
                    "type".to_string(),
                    JsonValue::JsonString(user_visible_stmt_or_msg_text(&param.type_text)),
                ),
            ])
        })
        .collect()
}

fn fact_items(facts: &[Fact]) -> Vec<JsonValue> {
    facts
        .iter()
        .map(|fact| JsonValue::JsonString(user_visible_stmt_or_msg_text(&fact.to_string())))
        .collect()
}
