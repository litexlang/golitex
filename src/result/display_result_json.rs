use crate::common::json_value::{
    line_file_line_json_value, line_file_source_json_value, render_json_value, JsonValue,
};
use crate::prelude::*;

const JSON_KEY_RESULT: &str = "result";
const JSON_KEY_SUCCESS: &str = "success";
const JSON_KEY_INFER_FACTS: &str = "infer_facts";
const JSON_KEY_VERIFIED_BY: &str = "verified_by";

fn verified_by_builtin_rule_value(rule: &str) -> JsonValue {
    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("builtin_rule".to_string()),
        ),
        ("rule".to_string(), JsonValue::JsonString(rule.to_string())),
    ])
}

fn verified_by_with_citation(
    type_name: &str,
    citation_line_file: &LineFile,
    cited_fact: JsonValue,
) -> JsonValue {
    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString(type_name.to_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(citation_line_file),
        ),
        (
            "file".to_string(),
            line_file_source_json_value(citation_line_file),
        ),
        ("cited_fact".to_string(), cited_fact),
    ])
}

fn verified_by_known_fact_object(
    citation_line_file: &LineFile,
    cited_fact: JsonValue,
    cited_fact_plain: &str,
    msg: &str,
) -> JsonValue {
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString("known_fact".to_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(citation_line_file),
        ),
        (
            "file".to_string(),
            line_file_source_json_value(citation_line_file),
        ),
        ("cited_fact".to_string(), cited_fact),
    ];
    if msg != cited_fact_plain {
        fields.push(("detail".to_string(), JsonValue::JsonString(msg.to_string())));
    }
    JsonValue::Object(fields)
}

impl StmtExecResult {
    pub fn to_display_json_string(&self) -> String {
        render_json_value(&self.to_json_value(), 0)
    }

    fn to_json_value(&self) -> JsonValue {
        match self {
            StmtExecResult::NonFactualStmtSuccess(x) => non_factual_stmt_success_to_json(x),
            StmtExecResult::FactualStmtSuccess(x) => factual_stmt_success_to_json(x),
            StmtExecResult::StmtUnknown(_) => unreachable!(),
        }
    }
}

fn non_factual_stmt_success_to_json(x: &NonFactualStmtSuccess) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_display_string = x.stmt.to_string();
    let stmt_text = match &x.stmt {
        Stmt::ProveStmt(_) => format!("{}{}\n{}", PROVE, COLON, stmt_display_string),
        _ => stmt_display_string,
    };

    let infer_items: Vec<JsonValue> = x
        .infers
        .infer_lines_unique_in_order()
        .iter()
        .map(|s| JsonValue::JsonString(s.clone()))
        .collect();

    let inside_items: Vec<JsonValue> = x.inside_results.iter().map(|r| r.to_json_value()).collect();

    let verified_by =
        verified_by_with_citation("non_factual", &stmt_line_file, JsonValue::Null);

    JsonValue::Object(vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            "type".to_string(),
            JsonValue::JsonString(x.stmt.stmt_type_name().to_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&stmt_line_file),
        ),
        ("stmt".to_string(), JsonValue::JsonString(stmt_text)),
        (JSON_KEY_VERIFIED_BY.to_string(), verified_by),
        (
            JSON_KEY_INFER_FACTS.to_string(),
            JsonValue::Array(infer_items),
        ),
        ("inside_results".to_string(), JsonValue::Array(inside_items)),
    ])
}

fn factual_stmt_success_to_json(x: &FactualStmtSuccess) -> JsonValue {
    if x.is_verified_by_builtin_rules_only() {
        factual_builtin_rules_to_json(x)
    } else {
        factual_known_fact_to_json(x)
    }
}

fn factual_builtin_rules_to_json(x: &FactualStmtSuccess) -> JsonValue {
    let fact_line_file = x.stmt.line_file();
    let verified_by = verified_by_builtin_rule_value(x.msg.as_str());

    let infer_items: Vec<JsonValue> = x
        .infers
        .infer_lines_unique_in_order()
        .iter()
        .map(|s| JsonValue::JsonString(s.clone()))
        .collect();

    let inside_items: Vec<JsonValue> = x.inside_results.iter().map(|r| r.to_json_value()).collect();

    JsonValue::Object(vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            "type".to_string(),
            JsonValue::JsonString("Fact".to_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&fact_line_file),
        ),
        (
            "stmt".to_string(),
            JsonValue::JsonString(x.stmt.to_string()),
        ),
        (JSON_KEY_VERIFIED_BY.to_string(), verified_by),
        (
            JSON_KEY_INFER_FACTS.to_string(),
            JsonValue::Array(infer_items),
        ),
        ("inside_results".to_string(), JsonValue::Array(inside_items)),
    ])
}

fn factual_known_fact_to_json(x: &FactualStmtSuccess) -> JsonValue {
    let known_fact_line_file = x.line_file_for_verified_by_known_fact_in_json();
    let stmt_line_file = x.stmt.line_file();
    let cited_fact_text = x
        .verified_by_fact
        .as_ref()
        .map(|f| f.to_string())
        .unwrap_or_else(|| x.msg.clone());
    let cited_fact_json = JsonValue::JsonString(cited_fact_text.clone());
    let verified_by = verified_by_known_fact_object(
        &known_fact_line_file,
        cited_fact_json,
        cited_fact_text.as_str(),
        x.msg.as_str(),
    );

    let infer_items: Vec<JsonValue> = x
        .infers
        .infer_lines_unique_in_order()
        .iter()
        .map(|s| JsonValue::JsonString(s.clone()))
        .collect();

    let inside_items: Vec<JsonValue> = x.inside_results.iter().map(|r| r.to_json_value()).collect();

    JsonValue::Object(vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            "type".to_string(),
            JsonValue::JsonString("Fact".to_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&stmt_line_file),
        ),
        (
            "stmt".to_string(),
            JsonValue::JsonString(x.stmt.to_string()),
        ),
        (
            "verified_by_fact_known_on_line".to_string(),
            line_file_line_json_value(&known_fact_line_file),
        ),
        (JSON_KEY_VERIFIED_BY.to_string(), verified_by),
        (
            JSON_KEY_INFER_FACTS.to_string(),
            JsonValue::Array(infer_items),
        ),
        ("inside_results".to_string(), JsonValue::Array(inside_items)),
    ])
}
