use crate::output::display_normalization::{
    json_value_is_empty_in_normal_output, remove_empty_json_fields,
};
use crate::output::json_value::JsonValue;
use crate::prelude::*;

use super::fields::JSON_KEY_STMT;

pub(in crate::output) fn render_unknown_result_json_value(
    unknown_result: &RuntimeErrorUnknownResult,
    output_detail: OutputDetail,
) -> JsonValue {
    match unknown_result {
        RuntimeErrorUnknownResult::Generic(unknown) => stmt_unknown_json_value(unknown),
        RuntimeErrorUnknownResult::Fact(unknown) => {
            fact_unknown_json_value(unknown.as_ref(), output_detail)
        }
    }
}

pub fn stmt_unknown_json_value(unknown: &UnknownGenericStmtResult) -> JsonValue {
    let mut fields = vec![(
        "type".to_string(),
        JsonValue::JsonString("unknown".to_string()),
    )];
    push_detail_field(&mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

pub fn fact_unknown_json_value(
    unknown: &UnknownFactResult,
    output_detail: OutputDetail,
) -> JsonValue {
    match unknown {
        UnknownFactResult::AtomicFact(x) => atomic_fact_unknown_json_value(x),
        UnknownFactResult::ExistFact(x) => exist_fact_unknown_json_value(x),
        UnknownFactResult::OrFact(x) => or_fact_unknown_json_value(x),
        UnknownFactResult::AndFact(x) => and_fact_unknown_json_value(x, output_detail),
        UnknownFactResult::ChainFact(x) => chain_fact_unknown_json_value(x, output_detail),
        UnknownFactResult::ForallFact(x) => forall_fact_unknown_json_value(x, output_detail),
        UnknownFactResult::ForallFactWithIff(x) => forall_iff_unknown_json_value(x, output_detail),
        UnknownFactResult::NotForall(x) => not_forall_unknown_json_value(x),
    }
}

fn atomic_fact_unknown_json_value(unknown: &UnknownAtomicFactResult) -> JsonValue {
    let mut fields = base_fact_unknown_fields("atomic fact unknown", &unknown.goal);
    push_detail_field(&mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn exist_fact_unknown_json_value(unknown: &UnknownExistFactResult) -> JsonValue {
    let mut fields = base_fact_unknown_fields("exist fact unknown", &unknown.goal);
    push_json_field(
        &mut fields,
        "witness_params",
        JsonValue::Array(param_items(&unknown.witness_params)),
    );
    push_json_field(
        &mut fields,
        "body",
        JsonValue::Array(fact_items(&unknown.body)),
    );
    push_detail_field(&mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn or_fact_unknown_json_value(unknown: &UnknownOrFactResult) -> JsonValue {
    let mut fields = base_fact_unknown_fields("or fact unknown", &unknown.goal);
    push_json_field(
        &mut fields,
        "branches",
        JsonValue::Array(fact_items(&unknown.branches)),
    );
    push_detail_field(&mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn and_fact_unknown_json_value(
    unknown: &UnknownAndFactResult,
    output_detail: OutputDetail,
) -> JsonValue {
    let mut fields = base_fact_unknown_fields("and fact unknown", &unknown.goal);
    push_part_field(
        &mut fields,
        "failed_part",
        unknown.failed_part.as_ref(),
        output_detail,
    );
    push_detail_field(&mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn chain_fact_unknown_json_value(
    unknown: &UnknownChainFactResult,
    output_detail: OutputDetail,
) -> JsonValue {
    let mut fields = base_fact_unknown_fields("chain fact unknown", &unknown.goal);
    push_part_field(
        &mut fields,
        "failed_chain_step",
        unknown.failed_part.as_ref(),
        output_detail,
    );
    push_detail_field(&mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn forall_fact_unknown_json_value(
    unknown: &UnknownForallFactResult,
    output_detail: OutputDetail,
) -> JsonValue {
    let mut fields = base_fact_unknown_fields("forall unknown", &unknown.goal);
    push_json_field(
        &mut fields,
        "params",
        JsonValue::Array(param_items(&unknown.params)),
    );
    push_json_field(
        &mut fields,
        "requirements",
        JsonValue::Array(fact_items(&unknown.requirements)),
    );
    push_part_field(
        &mut fields,
        "failed_prove",
        unknown.failed_prove.as_ref(),
        output_detail,
    );
    push_detail_field(&mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn forall_iff_unknown_json_value(
    unknown: &UnknownForallFactWithIffResult,
    output_detail: OutputDetail,
) -> JsonValue {
    let mut fields = base_fact_unknown_fields("forall iff unknown", &unknown.goal);
    push_json_field(
        &mut fields,
        "params",
        JsonValue::Array(param_items(&unknown.params)),
    );
    push_json_field(
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
            fact_unknown_json_value(child_unknown.as_ref(), output_detail),
        ));
    }
    push_detail_field(&mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn not_forall_unknown_json_value(unknown: &UnknownNotForallFactResult) -> JsonValue {
    let mut fields = base_fact_unknown_fields("not forall unknown", &unknown.goal);
    push_detail_field(&mut fields, unknown.detail.as_deref());
    JsonValue::Object(fields)
}

fn base_fact_unknown_fields(label: &str, goal: &Fact) -> Vec<(String, JsonValue)> {
    vec![
        ("type".to_string(), JsonValue::JsonString(label.to_string())),
        ("goal".to_string(), JsonValue::JsonString(goal.to_string())),
    ]
}

fn push_part_field(
    fields: &mut Vec<(String, JsonValue)>,
    key: &str,
    part: Option<&UnknownFactPart>,
    output_detail: OutputDetail,
) {
    if let Some(part) = part {
        fields.push((key.to_string(), part_json_value(part, output_detail)));
    }
}

fn part_json_value(part: &UnknownFactPart, output_detail: OutputDetail) -> JsonValue {
    let mut fields = Vec::new();
    if output_detail.is_detailed() {
        fields.push(("index".to_string(), JsonValue::Number(part.index)));
        fields.push(("count".to_string(), JsonValue::Number(part.count)));
    }
    fields.push((
        JSON_KEY_STMT.to_string(),
        JsonValue::JsonString(part.stmt.to_string()),
    ));
    if let Some(unknown) = &part.unknown {
        if should_show_nested_part_unknown(part, unknown.as_ref(), output_detail) {
            fields.push((
                "unknown_result".to_string(),
                fact_unknown_json_value(unknown.as_ref(), output_detail),
            ));
        }
    }
    JsonValue::Object(fields)
}

fn should_show_nested_part_unknown(
    part: &UnknownFactPart,
    unknown: &UnknownFactResult,
    output_detail: OutputDetail,
) -> bool {
    if output_detail.is_detailed() {
        return true;
    }
    !is_trivial_atomic_unknown_for_same_fact(part, unknown)
}

fn is_trivial_atomic_unknown_for_same_fact(
    part: &UnknownFactPart,
    unknown: &UnknownFactResult,
) -> bool {
    let UnknownFactResult::AtomicFact(atomic_unknown) = unknown else {
        return false;
    };
    atomic_unknown.detail.is_none() && atomic_unknown.goal.to_string() == part.stmt.to_string()
}

fn push_detail_field(fields: &mut Vec<(String, JsonValue)>, detail: Option<&[String]>) {
    let detail_items = detail
        .unwrap_or(&[])
        .iter()
        .map(|line| JsonValue::JsonString(line.clone()))
        .collect::<Vec<_>>();
    push_json_field(fields, "detail", JsonValue::Array(detail_items));
}

fn push_json_field(fields: &mut Vec<(String, JsonValue)>, key: &str, value: JsonValue) {
    let value = remove_empty_json_fields(value);
    if !json_value_is_empty_in_normal_output(&value) {
        fields.push((key.to_string(), value));
    }
}

fn param_items(params: &[UnknownFactParam]) -> Vec<JsonValue> {
    params
        .iter()
        .map(|param| {
            JsonValue::Object(vec![
                (
                    "name".to_string(),
                    JsonValue::JsonString(param.name.clone()),
                ),
                (
                    "type".to_string(),
                    JsonValue::JsonString(param.type_text.clone()),
                ),
            ])
        })
        .collect()
}

fn fact_items(facts: &[Fact]) -> Vec<JsonValue> {
    facts
        .iter()
        .map(|fact| JsonValue::JsonString(fact.to_string()))
        .collect()
}
