use crate::common::json_value::{
    json_one_level_indent, json_string_literal, line_file_line_json_fragment,
    line_file_line_json_value, line_file_source_json_fragment, line_file_source_json_value,
    render_json_value, JsonValue,
};
use crate::prelude::*;
use std::rc::Rc;

const JSON_KEY_RESULT: &str = "result";
const JSON_KEY_SUCCESS: &str = "success";
const JSON_KEY_INFER_FACTS: &str = "infer_facts";
const JSON_KEY_VERIFIED_BY: &str = "verified_by";

const JSON_KEY_ERROR_TYPE: &str = "error_type";
const JSON_KEY_MESSAGE: &str = "message";
const JSON_KEY_LINE: &str = "line";
const JSON_KEY_SOURCE: &str = "source";
const JSON_KEY_STMT_TYPE: &str = "type";
const JSON_KEY_STMT: &str = "stmt";
const JSON_KEY_INSIDE_RESULTS: &str = "inside_results";
const JSON_KEY_PREVIOUS_ERROR: &str = "previous_error";
const JSON_VALUE_ERROR: &str = "error";

fn user_visible_stmt_or_msg_text(raw: &str) -> String {
    raw.to_string()
}

/// `infer_facts` for JSON: all inferred lines except the one that only repeats the same text as
/// this entry's `stmt` field (that fact is already shown under `stmt` and stored in the fact store).
fn json_infer_fact_items_excluding_self_stmt(
    infers: &InferResult,
    stmt_text_as_in_json: &str,
) -> Vec<JsonValue> {
    let exclude = user_visible_stmt_or_msg_text(stmt_text_as_in_json);
    infers
        .infer_lines_unique_in_order()
        .iter()
        .filter(|s| user_visible_stmt_or_msg_text(s) != exclude)
        .map(|s| JsonValue::JsonString(user_visible_stmt_or_msg_text(s)))
        .collect()
}

/// Apply [`strip_free_param_numeric_tags_in_display`] once on a finished JSON blob (CLI/REPL/file run).
/// Nested JSON is built with `strip_free_param_tags == false` so a single final strip covers the whole tree.
fn finalize_display_text_with_optional_strip(
    text: String,
    strip_free_param_tags: bool,
) -> String {
    if strip_free_param_tags {
        strip_free_param_numeric_tags_in_display(&text)
    } else {
        text
    }
}

pub fn display_stmt_exec_result_json(
    runtime: &Runtime,
    r: &StmtResult,
    strip_free_param_tags: bool,
) -> String {
    let raw = render_json_value(&stmt_exec_result_json_value(runtime, r), 0);
    finalize_display_text_with_optional_strip(raw, strip_free_param_tags)
}

pub fn display_runtime_error_json(
    runtime: &Runtime,
    error: &RuntimeError,
    strip_free_param_tags: bool,
) -> String {
    let raw = build_display_error_json_object(runtime, error, 0, true);
    finalize_display_text_with_optional_strip(raw, strip_free_param_tags)
}

// Citation is in the same logical entry as this run (real path, "repl", "-e", etc.).
const KNOWN_FACT_SOURCE_ENTRY: &str = "entry";

fn known_fact_citation_source_json_value(line_file: &LineFile, mm: &ModuleManager) -> JsonValue {
    if is_default_line_file(line_file) {
        return line_file_source_json_value(line_file);
    }
    if let Some(entry_rc) = mm.display_entry_rc.as_ref() {
        if Rc::ptr_eq(&line_file.1, entry_rc) || line_file.1.as_ref() == entry_rc.as_ref() {
            return JsonValue::JsonString(KNOWN_FACT_SOURCE_ENTRY.to_string());
        }
    }
    if !mm.entry_path.is_empty() && line_file.1.as_ref() == mm.entry_path.as_str() {
        return JsonValue::JsonString(KNOWN_FACT_SOURCE_ENTRY.to_string());
    }
    line_file_source_json_value(line_file)
}

fn verified_by_builtin_rule_value(rule: &str) -> JsonValue {
    JsonValue::Object(vec![
        (
            "type".to_string(),
            JsonValue::JsonString("builtin_rule".to_string()),
        ),
        ("rule".to_string(), JsonValue::JsonString(rule.to_string())),
    ])
}

/// `verified_by` field for one [`FactualStmtSuccess`] (builtin rule or known fact).
fn factual_success_verified_by_value(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    if x.is_verified_by_builtin_rules_only() {
        return verified_by_builtin_rule_value(x.msg.as_str());
    }
    let known_fact_line_file = x.line_file_for_verified_by_known_fact_in_json();
    let cited_fact_text = x
        .verified_by_fact
        .as_ref()
        .map(|f| f.to_string())
        .unwrap_or_else(|| x.msg.clone());
    let cited_fact_text = user_visible_stmt_or_msg_text(&cited_fact_text);
    let msg_for_display = user_visible_stmt_or_msg_text(x.msg.as_str());
    let cited_fact_json = JsonValue::JsonString(cited_fact_text.clone());
    verified_by_known_fact_object(
        runtime,
        &known_fact_line_file,
        cited_fact_json,
        cited_fact_text.as_str(),
        msg_for_display.as_str(),
    )
}

/// Map one child [`StmtResult`] to the per-step `verified_by` object used in `verified_by` JSON arrays
/// (forall / and / chain composite facts).
fn stmt_result_to_composite_step_verified_by(runtime: &Runtime, r: &StmtResult) -> JsonValue {
    match r {
        StmtResult::FactualStmtSuccess(f) => factual_success_verified_by_value(runtime, f),
        StmtResult::NonFactualStmtSuccess(n) => JsonValue::Object(vec![
            (
                "type".to_string(),
                JsonValue::JsonString("non_factual".to_string()),
            ),
            (
                "stmt_type".to_string(),
                JsonValue::JsonString(n.stmt.stmt_type_name().to_string()),
            ),
        ]),
        StmtResult::StmtUnknown(_) => JsonValue::Object(vec![(
            "type".to_string(),
            JsonValue::JsonString("unknown".to_string()),
        )]),
    }
}

/// JSON for [`Fact::ForallFact`], [`Fact::AndFact`], or [`Fact::ChainFact`] when
/// `inside_results` holds one entry per sub-fact (then / conjunct / chain step).
fn composite_factual_with_step_proofs_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let fact_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let verified_by_items: Vec<JsonValue> = x
        .inside_results
        .iter()
        .map(|r| stmt_result_to_composite_step_verified_by(runtime, r))
        .collect();

    let infer_items: Vec<JsonValue> =
        json_infer_fact_items_excluding_self_stmt(&x.infers, &stmt_user_visible);

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
            JsonValue::JsonString(stmt_user_visible.clone()),
        ),
        (
            JSON_KEY_VERIFIED_BY.to_string(),
            JsonValue::Array(verified_by_items),
        ),
        (
            JSON_KEY_INFER_FACTS.to_string(),
            JsonValue::Array(infer_items),
        ),
        (
            JSON_KEY_INSIDE_RESULTS.to_string(),
            JsonValue::Array(vec![]),
        ),
    ])
}

fn verified_by_known_fact_object(
    runtime: &Runtime,
    citation_line_file: &LineFile,
    cited_fact: JsonValue,
    cited_fact_plain: &str,
    msg: &str,
) -> JsonValue {
    let source_value =
        known_fact_citation_source_json_value(citation_line_file, &runtime.module_manager);
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString("known_fact".to_string()),
        ),
        (
            "line".to_string(),
            line_file_line_json_value(citation_line_file),
        ),
        (JSON_KEY_SOURCE.to_string(), source_value),
        ("cited_fact".to_string(), cited_fact),
    ];
    if msg != cited_fact_plain {
        fields.push(("detail".to_string(), JsonValue::JsonString(msg.to_string())));
    }
    JsonValue::Object(fields)
}

fn stmt_exec_result_json_value(runtime: &Runtime, r: &StmtResult) -> JsonValue {
    match r {
        StmtResult::NonFactualStmtSuccess(x) => non_factual_stmt_success_to_json(runtime, x),
        StmtResult::FactualStmtSuccess(x) => factual_stmt_success_to_json(runtime, x),
        StmtResult::StmtUnknown(_) => unreachable!(),
    }
}

fn non_factual_stmt_success_to_json(runtime: &Runtime, x: &NonFactualStmtSuccess) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_display_string = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let stmt_text = match &x.stmt {
        Stmt::ProveStmt(_) => format!("{}{}\n{}", PROVE, COLON, stmt_display_string),
        _ => stmt_display_string,
    };

    let infer_items: Vec<JsonValue> = json_infer_fact_items_excluding_self_stmt(&x.infers, &stmt_text);

    let inside_items: Vec<JsonValue> = x
        .inside_results
        .iter()
        .map(|r| stmt_exec_result_json_value(runtime, r))
        .collect();

    let mut fields = vec![
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
        (
            JSON_KEY_INFER_FACTS.to_string(),
            JsonValue::Array(infer_items),
        ),
    ];

    // For `HaveExistObjStmt`, surface explicit exist-proof source(s) at top level.
    if x.stmt.stmt_type_name() == "HaveExistObjStmt" {
        let verified_by_items: Vec<JsonValue> = x
            .inside_results
            .iter()
            .map(|r| stmt_result_to_composite_step_verified_by(runtime, r))
            .collect();
        fields.push((
            JSON_KEY_VERIFIED_BY.to_string(),
            JsonValue::Array(verified_by_items),
        ));
    }

    fields.push((
        JSON_KEY_INSIDE_RESULTS.to_string(),
        JsonValue::Array(inside_items),
    ));

    JsonValue::Object(fields)
}

fn factual_stmt_success_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    if matches!(
        &x.stmt,
        Fact::ForallFact(_) | Fact::AndFact(_) | Fact::ChainFact(_)
    ) && !x.inside_results.is_empty()
    {
        return composite_factual_with_step_proofs_to_json(runtime, x);
    }
    if x.is_verified_by_builtin_rules_only() {
        factual_builtin_rules_to_json(runtime, x)
    } else {
        factual_known_fact_to_json(runtime, x)
    }
}

fn factual_builtin_rules_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let fact_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let verified_by = factual_success_verified_by_value(runtime, x);

    let infer_items: Vec<JsonValue> =
        json_infer_fact_items_excluding_self_stmt(&x.infers, &stmt_user_visible);

    let inside_items: Vec<JsonValue> = x
        .inside_results
        .iter()
        .map(|r| stmt_exec_result_json_value(runtime, r))
        .collect();

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
            JsonValue::JsonString(stmt_user_visible.clone()),
        ),
        (JSON_KEY_VERIFIED_BY.to_string(), verified_by),
        (
            JSON_KEY_INFER_FACTS.to_string(),
            JsonValue::Array(infer_items),
        ),
        ("inside_results".to_string(), JsonValue::Array(inside_items)),
    ])
}

fn factual_known_fact_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let verified_by = factual_success_verified_by_value(runtime, x);

    let infer_items: Vec<JsonValue> =
        json_infer_fact_items_excluding_self_stmt(&x.infers, &stmt_user_visible);

    let inside_items: Vec<JsonValue> = x
        .inside_results
        .iter()
        .map(|r| stmt_exec_result_json_value(runtime, r))
        .collect();

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
            JsonValue::JsonString(stmt_user_visible.clone()),
        ),
        (JSON_KEY_VERIFIED_BY.to_string(), verified_by),
        (
            JSON_KEY_INFER_FACTS.to_string(),
            JsonValue::Array(infer_items),
        ),
        ("inside_results".to_string(), JsonValue::Array(inside_items)),
    ])
}

fn json_array_field_line(indent_inner: &str, json_key: &str, json_elements: &[String]) -> String {
    if json_elements.is_empty() {
        format!("{}\"{}\": []", indent_inner, json_key)
    } else {
        let joined_elements = json_elements.join(",\n");
        format!(
            "{}\"{}\": [\n{}\n{}]",
            indent_inner, json_key, joined_elements, indent_inner
        )
    }
}

fn stmt_json_field_lines(indent_inner: &str, stmt: &Stmt) -> Vec<String> {
    let stmt_display_string = user_visible_stmt_or_msg_text(&stmt.to_string());
    let wrapped_stmt_display_string = match stmt {
        Stmt::ProveStmt(_) => format!("{}{}\n{}", PROVE, COLON, stmt_display_string),
        _ => stmt_display_string,
    };
    let mut lines: Vec<String> = Vec::new();
    lines.push(format!(
        "{}\"{}\": {}",
        indent_inner,
        JSON_KEY_STMT_TYPE,
        json_string_literal(&stmt.stmt_type_name())
    ));
    lines.push(format!(
        "{}\"{}\": {}",
        indent_inner,
        JSON_KEY_STMT,
        json_string_literal(&wrapped_stmt_display_string)
    ));
    lines
}

fn push_optional_statement_json_field_lines(
    field_lines: &mut Vec<String>,
    indent_inner: &str,
    statement: &Option<Stmt>,
) {
    match statement {
        Some(stmt) => {
            let stmt_lines = stmt_json_field_lines(indent_inner, stmt);
            for stmt_line in stmt_lines {
                field_lines.push(stmt_line);
            }
        }
        None => {}
    }
}

fn build_display_error_json_object(
    runtime: &Runtime,
    error: &RuntimeError,
    depth: usize,
    include_previous_error: bool,
) -> String {
    let indent_outer = json_one_level_indent(depth);
    let indent_inner = json_one_level_indent(depth + 1);
    let mut field_lines: Vec<String> = Vec::new();

    field_lines.push(format!(
        "{}\"{}\": {}",
        indent_inner,
        JSON_KEY_ERROR_TYPE,
        json_string_literal(error.display_label())
    ));
    field_lines.push(format!(
        "{}\"{}\": {}",
        indent_inner,
        JSON_KEY_RESULT,
        json_string_literal(JSON_VALUE_ERROR)
    ));

    let line_file = error.line_file();
    field_lines.push(format!(
        "{}\"{}\": {}",
        indent_inner,
        JSON_KEY_LINE,
        line_file_line_json_fragment(&line_file)
    ));
    field_lines.push(format!(
        "{}\"{}\": {}",
        indent_inner,
        JSON_KEY_SOURCE,
        line_file_source_json_fragment(&line_file)
    ));

    match error {
        RuntimeError::DefineParamsError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
        }
        RuntimeError::NameAlreadyUsedError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
        }
        RuntimeError::ArithmeticError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
            push_optional_statement_json_field_lines(
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
        RuntimeError::NewFactError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
            push_optional_statement_json_field_lines(
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
        RuntimeError::StoreFactError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
            push_optional_statement_json_field_lines(
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
        RuntimeError::ParseError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
        }
        RuntimeError::ExecStmtError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
            if let Some(stmt) = &e.statement {
                let stmt_lines = stmt_json_field_lines(indent_inner.as_str(), stmt);
                for stmt_line in stmt_lines {
                    field_lines.push(stmt_line);
                }
            }

            let mut inside_result_elements: Vec<String> = Vec::new();
            for inside_result in e.inside_results.iter() {
                inside_result_elements
                    .push(display_stmt_exec_result_json(runtime, inside_result, false));
            }
            field_lines.push(json_array_field_line(
                indent_inner.as_str(),
                JSON_KEY_INSIDE_RESULTS,
                &inside_result_elements,
            ));
        }
        RuntimeError::WellDefinedError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
        }
        RuntimeError::VerifyError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
        }
        RuntimeError::UnknownError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
            push_optional_statement_json_field_lines(
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
        RuntimeError::InferError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
        }
        RuntimeError::InstantiateError(e) => {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner,
                JSON_KEY_MESSAGE,
                json_string_literal(&user_visible_stmt_or_msg_text(&e.msg))
            ));
            push_optional_statement_json_field_lines(
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
    }

    let previous_error_line = build_previous_error_field_line(
        runtime,
        indent_inner.as_str(),
        error,
        depth + 1,
        include_previous_error,
    );
    field_lines.push(previous_error_line);

    format!(
        "{}{{\n{}\n{}}}",
        indent_outer,
        field_lines.join(",\n"),
        indent_outer
    )
}

fn build_previous_error_field_line(
    runtime: &Runtime,
    indent_inner: &str,
    error: &RuntimeError,
    previous_error_depth: usize,
    include_previous_error: bool,
) -> String {
    if !include_previous_error {
        return format!("{}\"{}\": null", indent_inner, JSON_KEY_PREVIOUS_ERROR);
    }

    let previous_error_reference = get_previous_error_reference(error);
    match previous_error_reference {
        Some(previous_error) => {
            let previous_error_json = build_display_error_json_object(
                runtime,
                previous_error,
                previous_error_depth,
                true,
            );
            format!(
                "{}\"{}\":\n{}",
                indent_inner, JSON_KEY_PREVIOUS_ERROR, previous_error_json
            )
        }
        None => format!("{}\"{}\": null", indent_inner, JSON_KEY_PREVIOUS_ERROR),
    }
}

fn get_previous_error_reference<'b>(error: &'b RuntimeError) -> Option<&'b RuntimeError> {
    match error {
        RuntimeError::DefineParamsError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::NameAlreadyUsedError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::ArithmeticError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::NewFactError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::StoreFactError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::ParseError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::ExecStmtError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::WellDefinedError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::VerifyError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::UnknownError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::InferError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
        RuntimeError::InstantiateError(e) => match &e.previous_error {
            Some(previous_error) => Some(previous_error.as_ref()),
            None => None,
        },
    }
}
