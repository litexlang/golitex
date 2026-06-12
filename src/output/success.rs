use crate::common::json_value::{line_file_line_json_value, render_json_value, JsonValue};
use crate::prelude::{
    CommandStmt, FactualStmtSuccess, NonFactualStmtSuccess, Runtime, Stmt, StmtResult,
    VerifiedByResult,
};

use super::evidence::{factual_success_forall_proof_fields, factual_success_verified_by_value};
use super::fields::{
    user_visible_stmt_or_msg_text, JSON_KEY_INSIDE_RESULTS, JSON_KEY_RESULT, JSON_KEY_STMT,
    JSON_KEY_STMT_TYPE, JSON_KEY_STORE_FACTS, JSON_KEY_SUCCESS, JSON_KEY_VERIFICATION,
};
use super::normalize::{finalize_display_text_with_optional_strip, json_value_for_output};
use super::source::stmt_text_for_json;
use super::store_facts::{store_fact_json_values, store_fact_json_values_for_fact};

pub fn display_stmt_exec_result_json(
    runtime: &Runtime,
    r: &StmtResult,
    strip_free_param_tags: bool,
) -> String {
    let value = json_value_for_output(runtime, stmt_exec_result_json_value(runtime, r));
    let raw = render_json_value(&value, 0);
    finalize_display_text_with_optional_strip(raw, strip_free_param_tags)
}

fn stmt_exec_result_json_value(runtime: &Runtime, r: &StmtResult) -> JsonValue {
    if let Some(x) = r.factual_success() {
        factual_stmt_success_to_json(runtime, x)
    } else if let Some(x) = r.non_factual_success() {
        non_factual_stmt_success_to_json(runtime, x)
    } else {
        unreachable!()
    }
}

fn non_factual_stmt_success_to_json(runtime: &Runtime, x: &NonFactualStmtSuccess) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_text = stmt_text_for_json(runtime, &x.stmt);
    let store_fact_items = store_fact_json_values(&x.infers);

    let mut fields = vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            JSON_KEY_STMT_TYPE.to_string(),
            JsonValue::JsonString(x.stmt.output_type_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&stmt_line_file),
        ),
        (JSON_KEY_STMT.to_string(), JsonValue::JsonString(stmt_text)),
        (
            JSON_KEY_STORE_FACTS.to_string(),
            JsonValue::Array(store_fact_items),
        ),
    ];

    fields.push((
        JSON_KEY_INSIDE_RESULTS.to_string(),
        inside_results_value(runtime, &x.stmt, &x.inside_results),
    ));

    JsonValue::Object(fields)
}

fn inside_results_value(
    runtime: &Runtime,
    stmt: &Stmt,
    inside_results: &[StmtResult],
) -> JsonValue {
    let should_show_inside_results =
        runtime.detail_output || matches!(stmt, Stmt::Command(CommandStmt::RunFileStmt(_)));
    if !should_show_inside_results {
        return JsonValue::Array(vec![]);
    }

    JsonValue::Array(
        inside_results
            .iter()
            .map(|r| stmt_exec_result_json_value(runtime, r))
            .collect::<Vec<_>>(),
    )
}

fn factual_stmt_success_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    if x.is_verified_by_builtin_rules_only() {
        factual_builtin_rules_to_json(runtime, x)
    } else {
        factual_citation_to_json(runtime, x)
    }
}

fn factual_builtin_rules_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let fact_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let store_fact_items = store_fact_json_values_for_fact(&x.infers, &x.stmt);

    let mut fields = vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            JSON_KEY_STMT_TYPE.to_string(),
            JsonValue::JsonString(x.stmt.output_type_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&fact_line_file),
        ),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(stmt_user_visible.clone()),
        ),
    ];

    fields.extend(factual_success_forall_proof_fields(runtime, x));
    if !factual_success_is_forall_proof(x) {
        fields.push((
            JSON_KEY_VERIFICATION.to_string(),
            factual_success_verified_by_value(runtime, x),
        ));
    }
    fields.push((
        JSON_KEY_STORE_FACTS.to_string(),
        JsonValue::Array(store_fact_items),
    ));
    fields.push(("inside_results".to_string(), JsonValue::Array(vec![])));

    JsonValue::Object(fields)
}

fn factual_citation_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let store_fact_items = store_fact_json_values_for_fact(&x.infers, &x.stmt);

    let mut fields = vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            JSON_KEY_STMT_TYPE.to_string(),
            JsonValue::JsonString(x.stmt.output_type_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(&stmt_line_file),
        ),
        (
            JSON_KEY_STMT.to_string(),
            JsonValue::JsonString(stmt_user_visible.clone()),
        ),
    ];

    fields.extend(factual_success_forall_proof_fields(runtime, x));
    if !factual_success_is_forall_proof(x) {
        fields.push((
            JSON_KEY_VERIFICATION.to_string(),
            factual_success_verified_by_value(runtime, x),
        ));
    }
    fields.push((
        JSON_KEY_STORE_FACTS.to_string(),
        JsonValue::Array(store_fact_items),
    ));
    fields.push(("inside_results".to_string(), JsonValue::Array(vec![])));

    JsonValue::Object(fields)
}

fn factual_success_is_forall_proof(x: &FactualStmtSuccess) -> bool {
    matches!(x.verified_by, VerifiedByResult::ForallProof(_))
}
