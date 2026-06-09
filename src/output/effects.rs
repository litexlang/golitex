use crate::common::json_value::JsonValue;
use crate::prelude::{
    AddsToContextEffect, BuiltinInferenceReason, ByDefinitionReason, Fact, InferEffect,
    InferReason, InferResult, InferRuleReason, OutputWarning,
};

use super::fields::user_visible_stmt_or_msg_text;

pub(crate) fn effects_json_values(infers: &InferResult) -> Vec<JsonValue> {
    infers
        .effects()
        .iter()
        .filter_map(effect_json_value)
        .collect::<Vec<_>>()
}

fn effect_json_value(effect: &InferEffect) -> Option<JsonValue> {
    match effect {
        InferEffect::AddsToContext(adds) => adds_to_context_json_value(adds),
        InferEffect::Warning(warning) => Some(warning_json_value(warning)),
    }
}

fn adds_to_context_json_value(adds: &AddsToContextEffect) -> Option<JsonValue> {
    let fact_items = unique_fact_strings(&adds.facts)
        .into_iter()
        .map(JsonValue::JsonString)
        .collect::<Vec<_>>();
    if fact_items.is_empty() {
        return None;
    }

    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString("adds to context".to_string()),
        ),
        (
            "reason".to_string(),
            JsonValue::JsonString(reason_label(&adds.reason).to_string()),
        ),
    ];

    if let Some(source) = reason_source_json_value(&adds.reason) {
        fields.push(("source".to_string(), source));
    }

    fields.push(("facts".to_string(), JsonValue::Array(fact_items)));
    Some(JsonValue::Object(fields))
}

fn warning_json_value(warning: &OutputWarning) -> JsonValue {
    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("warning".to_string()),
        ),
        (
            "message".to_string(),
            JsonValue::JsonString(warning.message.clone()),
        ),
    ])
}

fn reason_label(reason: &InferReason) -> &str {
    match reason {
        InferReason::VerifiedStatement => "verified statement",
        InferReason::ProvedClaim => "proved claim",
        InferReason::UnsafeAssumption => "unsafe assumption",
        InferReason::LetBinding => "let binding",
        InferReason::ObjectIntroduction => "object introduction",
        InferReason::ExistElimination => "exist elimination",
        InferReason::TheoremInstantiation => "theorem instantiation",
        InferReason::ByDefinition(_) => "by definition",
        InferReason::BuiltinInference(_) => "builtin inference",
        InferReason::InferRule(_) => "infer rule",
        InferReason::Evaluation => "evaluation",
        InferReason::ParameterDeclaration => "parameter declaration",
        InferReason::Other(s) => s.as_str(),
    }
}

fn reason_source_json_value(reason: &InferReason) -> Option<JsonValue> {
    match reason {
        InferReason::ByDefinition(reason) => by_definition_source_json_value(reason),
        InferReason::BuiltinInference(reason) => builtin_inference_source_json_value(reason),
        InferReason::InferRule(reason) => infer_rule_source_json_value(reason),
        _ => None,
    }
}

fn by_definition_source_json_value(reason: &ByDefinitionReason) -> Option<JsonValue> {
    let mut fields = Vec::new();
    push_source_fact_field(&mut fields, reason.source_fact.as_deref());
    if let Some(definition) = &reason.definition {
        fields.push((
            "definition".to_string(),
            JsonValue::JsonString(definition.clone()),
        ));
    }
    object_or_none(fields)
}

fn builtin_inference_source_json_value(reason: &BuiltinInferenceReason) -> Option<JsonValue> {
    let mut fields = Vec::new();
    push_source_fact_field(&mut fields, reason.source_fact.as_deref());
    fields.push((
        "rule".to_string(),
        JsonValue::JsonString(reason.rule.clone()),
    ));
    object_or_none(fields)
}

fn infer_rule_source_json_value(reason: &InferRuleReason) -> Option<JsonValue> {
    let mut fields = Vec::new();
    push_source_fact_field(&mut fields, reason.source_fact.as_deref());
    fields.push((
        "rule".to_string(),
        JsonValue::JsonString(reason.rule.clone()),
    ));
    object_or_none(fields)
}

fn push_source_fact_field(fields: &mut Vec<(String, JsonValue)>, fact: Option<&Fact>) {
    if let Some(fact) = fact {
        fields.push((
            "fact".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&fact.to_string())),
        ));
    }
}

fn object_or_none(fields: Vec<(String, JsonValue)>) -> Option<JsonValue> {
    if fields.is_empty() {
        None
    } else {
        Some(JsonValue::Object(fields))
    }
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
