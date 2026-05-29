use crate::common::json_value::{
    json_one_level_indent, json_string_literal, line_file_line_json_value, render_json_value,
    JsonValue,
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
fn finalize_display_text_with_optional_strip(text: String, strip_free_param_tags: bool) -> String {
    if strip_free_param_tags {
        strip_free_param_numeric_tags_in_display(&text)
    } else {
        text
    }
}

fn should_hide_file_paths(runtime: &Runtime) -> bool {
    !runtime.detail_output
}

fn json_value_for_output(runtime: &Runtime, value: JsonValue) -> JsonValue {
    if runtime.detail_output {
        value
    } else {
        remove_empty_json_fields(value)
    }
}

fn remove_empty_json_fields(value: JsonValue) -> JsonValue {
    match value {
        JsonValue::Object(fields) => {
            let mut next_fields: Vec<(String, JsonValue)> = Vec::new();
            for (key, field_value) in fields {
                let field_value = remove_empty_json_fields(field_value);
                if !json_value_is_empty_in_normal_output(&field_value) {
                    next_fields.push((key, field_value));
                }
            }
            JsonValue::Object(next_fields)
        }
        JsonValue::Array(items) => JsonValue::Array(
            items
                .into_iter()
                .map(remove_empty_json_fields)
                .collect::<Vec<_>>(),
        ),
        _ => value,
    }
}

fn json_value_is_empty_in_normal_output(value: &JsonValue) -> bool {
    match value {
        JsonValue::JsonString(s) => s.is_empty(),
        JsonValue::Array(items) => items.is_empty(),
        _ => false,
    }
}

pub fn display_stmt_exec_result_json(
    runtime: &Runtime,
    r: &StmtResult,
    strip_free_param_tags: bool,
) -> String {
    let value = json_value_for_output(runtime, stmt_exec_result_json_value(runtime, r));
    let raw = render_json_value(&value, 0);
    finalize_display_text_with_optional_strip(raw, strip_free_param_tags)
}

pub fn display_runtime_error_json(
    runtime: &Runtime,
    error: &RuntimeError,
    strip_free_param_tags: bool,
) -> String {
    let raw = build_display_error_json_object(runtime, error, 0, true, None);
    finalize_display_text_with_optional_strip(raw, strip_free_param_tags)
}

const SOURCE_KIND: &str = "source_kind";
const SOURCE_KIND_ENTRY: &str = "entry";
const SOURCE_KIND_BUILTIN: &str = "builtin";
const SOURCE_KIND_RUN_FILE: &str = "run_file";

fn line_files_have_same_source(left: &LineFile, right: &LineFile) -> bool {
    Rc::ptr_eq(&left.1, &right.1) || left.1.as_ref() == right.1.as_ref()
}

fn line_file_is_entry_source(line_file: &LineFile, mm: &ModuleManager) -> bool {
    if let Some(entry_rc) = mm.display_entry_rc.as_ref() {
        if Rc::ptr_eq(&line_file.1, entry_rc) || line_file.1.as_ref() == entry_rc.as_ref() {
            return true;
        }
    }
    !mm.entry_path.is_empty() && line_file.1.as_ref() == mm.entry_path.as_str()
}

fn display_source_label_for_line_file(
    runtime: &Runtime,
    line_file: &LineFile,
) -> Option<(String, String)> {
    if is_default_line_file(line_file) {
        return None;
    }

    let path = line_file.1.as_ref();
    if path == BUILTIN_CODE_PATH {
        return Some((
            SOURCE_KIND_BUILTIN.to_string(),
            BUILTIN_CODE_PATH.to_string(),
        ));
    }

    if line_file_is_entry_source(line_file, &runtime.module_manager) {
        return Some((SOURCE_KIND_ENTRY.to_string(), SOURCE_KIND_ENTRY.to_string()));
    }

    if let Some(label) = runtime.module_manager.display_source_labels.get(path) {
        return Some((label.source_kind.clone(), label.source.clone()));
    }

    Some((
        SOURCE_KIND_RUN_FILE.to_string(),
        "external_file".to_string(),
    ))
}

fn source_ref_json_fields(
    runtime: &Runtime,
    source_line_file: &LineFile,
    current_line_file: Option<&LineFile>,
) -> Vec<(String, JsonValue)> {
    let mut fields = vec![(
        JSON_KEY_LINE.to_string(),
        line_file_line_json_value(source_line_file),
    )];

    let same_source = match current_line_file {
        Some(current_line_file) => line_files_have_same_source(source_line_file, current_line_file),
        None => line_file_is_entry_source(source_line_file, &runtime.module_manager),
    };

    if !same_source {
        if let Some((source_kind, source)) =
            display_source_label_for_line_file(runtime, source_line_file)
        {
            fields.push((
                SOURCE_KIND.to_string(),
                JsonValue::JsonString(source_kind.clone()),
            ));
            fields.push((JSON_KEY_SOURCE.to_string(), JsonValue::JsonString(source)));
            if runtime.detail_output && source_kind != SOURCE_KIND_BUILTIN {
                fields.push((
                    "path".to_string(),
                    JsonValue::JsonString(source_line_file.1.as_ref().to_string()),
                ));
            }
        }
    }

    fields
}

fn source_ref_json_value(
    runtime: &Runtime,
    source_line_file: &LineFile,
    current_line_file: Option<&LineFile>,
) -> JsonValue {
    JsonValue::Object(source_ref_json_fields(
        runtime,
        source_line_file,
        current_line_file,
    ))
}

fn verified_by_builtin_rule_value(rule: &str, verify_what: Option<&Fact>) -> JsonValue {
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString("builtin rule".to_string()),
        ),
        ("rule".to_string(), JsonValue::JsonString(rule.to_string())),
    ];
    if let Some(vw) = verify_what {
        fields.push((
            "verify_what".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&vw.to_string())),
        ));
    }
    JsonValue::Object(fields)
}

/// `verified_by` field for one [`FactualStmtSuccess`] (builtin rule or citation).
fn factual_success_verified_by_value(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let current_line_file = x.stmt.line_file();
    verified_by_result_json_value(runtime, &x.verified_by, &current_line_file)
}

fn verified_by_result_json_value(
    runtime: &Runtime,
    verified_by: &VerifiedByResult,
    current_line_file: &LineFile,
) -> JsonValue {
    match verified_by {
        VerifiedByResult::BuiltinRule(r) => verified_by_builtin_rule_value(&r.msg, None),
        VerifiedByResult::Fact(r) => {
            let citation_type = citation_type_for_stmt(r.cite_what.as_ref());
            let cited_stmt_plain = user_visible_stmt_or_msg_text(&r.cite_what.to_string());
            let citation_line_file = r.cite_what.line_file();
            let display_text = r
                .detail
                .as_deref()
                .filter(|s| !s.is_empty())
                .map(|s| user_visible_stmt_or_msg_text(s))
                .unwrap_or_else(|| cited_stmt_plain.clone());
            let cited_stmt_json = JsonValue::JsonString(cited_stmt_plain.clone());
            verified_by_citation_object(
                runtime,
                &citation_line_file,
                current_line_file,
                citation_type.as_str(),
                cited_stmt_json,
                cited_stmt_plain.as_str(),
                display_text.as_str(),
                None,
            )
        }
        VerifiedByResult::VerifiedBys(w) => JsonValue::Array(
            w.cite_what
                .iter()
                .map(|item| verified_bys_enum_json_value(runtime, item, current_line_file))
                .collect(),
        ),
    }
}

fn verified_bys_enum_json_value(
    runtime: &Runtime,
    item: &VerifiedBysEnum,
    current_line_file: &LineFile,
) -> JsonValue {
    match item {
        VerifiedBysEnum::ByBuiltinRule(r) => {
            verified_by_builtin_rule_value(&r.msg, Some(&r.verify_what))
        }
        VerifiedBysEnum::ByFact(r) => {
            let citation_type = citation_type_for_stmt(r.cite_what.as_ref());
            let cited_stmt_plain = user_visible_stmt_or_msg_text(&r.cite_what.to_string());
            let citation_line_file = r.cite_what.line_file();
            let display_text = r
                .detail
                .as_deref()
                .filter(|s| !s.is_empty())
                .map(|s| user_visible_stmt_or_msg_text(s))
                .unwrap_or_else(|| cited_stmt_plain.clone());
            verified_by_citation_object(
                runtime,
                &citation_line_file,
                current_line_file,
                citation_type.as_str(),
                JsonValue::JsonString(cited_stmt_plain.clone()),
                cited_stmt_plain.as_str(),
                display_text.as_str(),
                Some(&r.verify_what),
            )
        }
    }
}

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

fn citation_type_for_stmt(stmt: &Stmt) -> String {
    match stmt {
        Stmt::Fact(fact) => format!("cite {}", citation_fact_type_label(fact)),
        Stmt::DefPropStmt(_) => "cite prop def".to_string(),
        Stmt::DefAbstractPropStmt(_) => "cite abstract prop def".to_string(),
        Stmt::DefLetStmt(_) => "cite let def".to_string(),
        Stmt::DefAlgoStmt(_) => "cite algo def".to_string(),
        Stmt::DefStructStmt(_) => "cite struct def".to_string(),
        _ => format!("cite {} stmt", stmt_type_label_for_citation(stmt)),
    }
}

fn citation_fact_type_label(fact: &Fact) -> &'static str {
    match fact {
        Fact::AtomicFact(_) => "atomic fact",
        Fact::ExistFact(_) => "exist fact",
        Fact::OrFact(_) => "or fact",
        Fact::AndFact(_) => "and fact",
        Fact::ChainFact(_) => "chain fact",
        Fact::ForallFact(_) => "forall fact",
        Fact::ForallFactWithIff(_) => "forall iff fact",
        Fact::NotForall(_) => "not forall fact",
    }
}

fn stmt_type_label_for_citation(stmt: &Stmt) -> String {
    let stmt_type_name = stmt.stmt_type_name();
    let base_name = stmt_type_name
        .strip_suffix("Stmt")
        .unwrap_or(stmt_type_name.as_str());
    lower_camel_case_words(base_name)
}

fn lower_camel_case_words(input: &str) -> String {
    let mut out = String::new();
    let mut prev_is_lower_or_digit = false;
    for ch in input.chars() {
        if ch.is_ascii_uppercase() {
            if prev_is_lower_or_digit && !out.is_empty() {
                out.push(' ');
            }
            out.push(ch.to_ascii_lowercase());
            prev_is_lower_or_digit = false;
        } else {
            out.push(ch);
            prev_is_lower_or_digit = ch.is_ascii_lowercase() || ch.is_ascii_digit();
        }
    }
    out
}

fn verified_by_citation_object(
    runtime: &Runtime,
    citation_line_file: &LineFile,
    current_line_file: &LineFile,
    citation_type: &str,
    cited_stmt: JsonValue,
    cited_stmt_plain: &str,
    msg: &str,
    verify_what: Option<&Fact>,
) -> JsonValue {
    let cite_source = source_ref_json_value(runtime, citation_line_file, Some(current_line_file));
    let mut fields = vec![
        (
            "type".to_string(),
            JsonValue::JsonString(citation_type.to_string()),
        ),
        ("cite_source".to_string(), cite_source),
        ("cited_stmt".to_string(), cited_stmt),
    ];
    if msg != cited_stmt_plain {
        fields.push(("detail".to_string(), JsonValue::JsonString(msg.to_string())));
    }
    if let Some(vw) = verify_what {
        fields.push((
            "verify_what".to_string(),
            JsonValue::JsonString(user_visible_stmt_or_msg_text(&vw.to_string())),
        ));
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
    let stmt_display_string = stmt_text_for_json(runtime, &x.stmt);
    let stmt_text = match &x.stmt {
        Stmt::ProveStmt(_) => format!("{}{}\n{}", PROVE, COLON, stmt_display_string),
        _ => stmt_display_string,
    };

    let infer_items: Vec<JsonValue> =
        json_infer_fact_items_excluding_self_stmt(&x.infers, &stmt_text);

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
    if x.is_verified_by_builtin_rules_only() {
        factual_builtin_rules_to_json(runtime, x)
    } else {
        factual_citation_to_json(runtime, x)
    }
}

fn factual_builtin_rules_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let fact_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let verified_by = factual_success_verified_by_value(runtime, x);

    let infer_items: Vec<JsonValue> =
        json_infer_fact_items_excluding_self_stmt(&x.infers, &stmt_user_visible);

    JsonValue::Object(vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            "type".to_string(),
            JsonValue::JsonString(x.stmt.fact_type_string()),
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
        ("inside_results".to_string(), JsonValue::Array(vec![])),
    ])
}

fn factual_citation_to_json(runtime: &Runtime, x: &FactualStmtSuccess) -> JsonValue {
    let stmt_line_file = x.stmt.line_file();
    let stmt_user_visible = user_visible_stmt_or_msg_text(&x.stmt.to_string());
    let verified_by = factual_success_verified_by_value(runtime, x);

    let infer_items: Vec<JsonValue> =
        json_infer_fact_items_excluding_self_stmt(&x.infers, &stmt_user_visible);

    JsonValue::Object(vec![
        (
            JSON_KEY_RESULT.to_string(),
            JsonValue::JsonString(JSON_KEY_SUCCESS.to_string()),
        ),
        (
            "type".to_string(),
            JsonValue::JsonString(x.stmt.fact_type_string()),
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
        ("inside_results".to_string(), JsonValue::Array(vec![])),
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

fn json_value_field_line(indent_inner: &str, json_key: &str, value: &JsonValue) -> String {
    let field_depth = indent_inner.len() / json_one_level_indent(1).len();
    let object_depth = field_depth.saturating_sub(1);
    let single_field_object = JsonValue::Object(vec![(json_key.to_string(), value.clone())]);
    let rendered = render_json_value(&single_field_object, object_depth);
    let mut lines = rendered.lines().collect::<Vec<_>>();
    if lines.len() < 3 {
        return rendered;
    }
    lines.remove(0);
    lines.pop();
    lines.join("\n")
}

fn push_json_value_field_line(
    runtime: &Runtime,
    field_lines: &mut Vec<String>,
    indent_inner: &str,
    json_key: &str,
    value: JsonValue,
) {
    if runtime.detail_output || !json_value_is_empty_in_normal_output(&value) {
        field_lines.push(json_value_field_line(indent_inner, json_key, &value));
    }
}

fn push_json_string_field_line(
    runtime: &Runtime,
    field_lines: &mut Vec<String>,
    indent_inner: &str,
    json_key: &str,
    value: &str,
) {
    push_json_value_field_line(
        runtime,
        field_lines,
        indent_inner,
        json_key,
        JsonValue::JsonString(user_visible_stmt_or_msg_text(value)),
    );
}

fn push_exec_stmt_error_message_field_line(
    runtime: &Runtime,
    field_lines: &mut Vec<String>,
    indent_inner: &str,
    statement: &Option<Stmt>,
    message: &str,
) {
    let message = exec_stmt_error_message_text_for_json(runtime, statement, message);
    push_json_value_field_line(
        runtime,
        field_lines,
        indent_inner,
        JSON_KEY_MESSAGE,
        JsonValue::JsonString(message),
    );
}

fn exec_stmt_error_message_text_for_json(
    runtime: &Runtime,
    statement: &Option<Stmt>,
    message: &str,
) -> String {
    let message = user_visible_stmt_or_msg_text(message);
    if runtime.detail_output {
        return message;
    }

    match statement {
        Some(Stmt::RunFileStmt(_)) if message.starts_with("Failed to read file:") => {
            "Failed to read file: external_file".to_string()
        }
        _ => message,
    }
}

fn push_source_ref_field_lines(
    runtime: &Runtime,
    field_lines: &mut Vec<String>,
    indent_inner: &str,
    source_line_file: &LineFile,
    current_line_file: Option<&LineFile>,
) {
    for (key, value) in source_ref_json_fields(runtime, source_line_file, current_line_file) {
        field_lines.push(json_value_field_line(indent_inner, key.as_str(), &value));
    }
}

fn stmt_text_for_json(runtime: &Runtime, stmt: &Stmt) -> String {
    if should_hide_file_paths(runtime) {
        if let Stmt::RunFileStmt(_) = stmt {
            return "run_file".to_string();
        }
    }
    user_visible_stmt_or_msg_text(&stmt.to_string())
}

fn stmt_json_field_lines(runtime: &Runtime, indent_inner: &str, stmt: &Stmt) -> Vec<String> {
    let stmt_display_string = stmt_text_for_json(runtime, stmt);
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
    runtime: &Runtime,
    field_lines: &mut Vec<String>,
    indent_inner: &str,
    statement: &Option<Stmt>,
) {
    match statement {
        Some(stmt) => {
            let stmt_lines = stmt_json_field_lines(runtime, indent_inner, stmt);
            for stmt_line in stmt_lines {
                field_lines.push(stmt_line);
            }
        }
        None => {}
    }
}

fn error_own_statement(error: &RuntimeError) -> Option<&Stmt> {
    match error {
        RuntimeError::DefineParamsError(e) => e.statement.as_ref(),
        RuntimeError::NameAlreadyUsedError(e) => e.statement.as_ref(),
        RuntimeError::ArithmeticError(e) => e.statement.as_ref(),
        RuntimeError::NewFactError(e) => e.statement.as_ref(),
        RuntimeError::StoreFactError(e) => e.statement.as_ref(),
        RuntimeError::ParseError(e) => e.statement.as_ref(),
        RuntimeError::ExecStmtError(e) => e.statement.as_ref(),
        RuntimeError::WellDefinedError(e) => e.statement.as_ref(),
        RuntimeError::VerifyError(e) => e.statement.as_ref(),
        RuntimeError::UnknownError(e) => e.statement.as_ref(),
        RuntimeError::InferError(e) => e.statement.as_ref(),
        RuntimeError::InstantiateError(e) => e.statement.as_ref(),
    }
}

fn build_display_error_json_object(
    runtime: &Runtime,
    error: &RuntimeError,
    depth: usize,
    include_previous_error: bool,
    statement_context: Option<&Stmt>,
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
    push_source_ref_field_lines(
        runtime,
        &mut field_lines,
        indent_inner.as_str(),
        &line_file,
        None,
    );

    match error {
        RuntimeError::DefineParamsError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
        }
        RuntimeError::NameAlreadyUsedError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
        }
        RuntimeError::ArithmeticError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
            push_optional_statement_json_field_lines(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
        RuntimeError::NewFactError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
            push_optional_statement_json_field_lines(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
        RuntimeError::StoreFactError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
            push_optional_statement_json_field_lines(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
        RuntimeError::ParseError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
        }
        RuntimeError::ExecStmtError(e) => {
            push_exec_stmt_error_message_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
                &e.msg,
            );
            if let Some(stmt) = &e.statement {
                let stmt_lines = stmt_json_field_lines(runtime, indent_inner.as_str(), stmt);
                for stmt_line in stmt_lines {
                    field_lines.push(stmt_line);
                }
            }

            let mut inside_result_elements: Vec<String> = Vec::new();
            for inside_result in e.inside_results.iter() {
                inside_result_elements.push(display_stmt_exec_result_json(
                    runtime,
                    inside_result,
                    false,
                ));
            }
            if runtime.detail_output || !inside_result_elements.is_empty() {
                field_lines.push(json_array_field_line(
                    indent_inner.as_str(),
                    JSON_KEY_INSIDE_RESULTS,
                    &inside_result_elements,
                ));
            }
        }
        RuntimeError::WellDefinedError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
            let well_defined_stmt = e.statement.as_ref().or(statement_context).cloned();
            push_optional_statement_json_field_lines(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                &well_defined_stmt,
            );
        }
        RuntimeError::VerifyError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
            push_optional_statement_json_field_lines(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
        RuntimeError::UnknownError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
            push_optional_statement_json_field_lines(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
        RuntimeError::InferError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
        }
        RuntimeError::InstantiateError(e) => {
            push_json_string_field_line(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                JSON_KEY_MESSAGE,
                &e.msg,
            );
            push_optional_statement_json_field_lines(
                runtime,
                &mut field_lines,
                indent_inner.as_str(),
                &e.statement,
            );
        }
    }

    let context_for_child = error_own_statement(error).or(statement_context);
    let previous_error_line = build_previous_error_field_line(
        runtime,
        indent_inner.as_str(),
        error,
        depth + 1,
        include_previous_error,
        context_for_child,
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
    context_for_child: Option<&Stmt>,
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
                context_for_child,
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
