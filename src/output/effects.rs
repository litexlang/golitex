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
        .filter_map(|effect| effect_json_value(effect, None))
        .collect::<Vec<_>>()
}

pub(crate) fn effects_json_values_for_fact(
    infers: &InferResult,
    primary_fact: &Fact,
) -> Vec<JsonValue> {
    infers
        .effects()
        .iter()
        .filter_map(|effect| effect_json_value(effect, Some(primary_fact)))
        .collect::<Vec<_>>()
}

fn effect_json_value(effect: &InferEffect, primary_fact: Option<&Fact>) -> Option<JsonValue> {
    match effect {
        InferEffect::AddsToContext(adds) => adds_to_context_json_value(adds, primary_fact),
        InferEffect::Warning(warning) => Some(warning_json_value(warning)),
    }
}

fn adds_to_context_json_value(
    adds: &AddsToContextEffect,
    primary_fact: Option<&Fact>,
) -> Option<JsonValue> {
    let fact_items = unique_fact_strings(&adds.facts)
        .into_iter()
        .map(JsonValue::JsonString)
        .collect::<Vec<_>>();
    if fact_items.is_empty() {
        return None;
    }

    if adds_exact_primary_fact(adds, primary_fact) {
        return Some(JsonValue::Object(vec![(
            "type".to_string(),
            JsonValue::JsonString("add proven fact to context".to_string()),
        )]));
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

fn adds_exact_primary_fact(adds: &AddsToContextEffect, primary_fact: Option<&Fact>) -> bool {
    let Some(primary_fact) = primary_fact else {
        return false;
    };
    adds.facts.len() == 1 && adds.facts[0].to_string() == primary_fact.to_string()
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
