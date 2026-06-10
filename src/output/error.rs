use crate::common::json_value::{
    json_one_level_indent, json_string_literal, render_json_value, JsonValue,
};
use crate::prelude::{CommandStmt, LineFile, Runtime, RuntimeError, RuntimeErrorOutput, Stmt};

use super::fields::{
    user_visible_stmt_or_msg_text, JSON_KEY_ERROR_TYPE, JSON_KEY_FAILED_GOAL, JSON_KEY_FAILED_STEP,
    JSON_KEY_INSIDE_RESULTS, JSON_KEY_MESSAGE, JSON_KEY_PREVIOUS_ERROR, JSON_KEY_RESULT,
    JSON_KEY_UNKNOWN_RESULT, JSON_VALUE_ERROR,
};
use super::normalize::{
    finalize_display_text_with_optional_strip, json_value_is_empty_in_normal_output,
};
use super::source::{source_ref_json_fields, stmt_json_field_lines, stmt_json_value};
use super::success::display_stmt_exec_result_json;
use super::unknown_result_json_value;

pub fn display_runtime_error_json(
    runtime: &Runtime,
    error: &RuntimeError,
    strip_free_param_tags: bool,
) -> String {
    let raw = build_display_error_json_object(runtime, error, 0, true, None);
    finalize_display_text_with_optional_strip(raw, strip_free_param_tags)
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
        Some(Stmt::Command(CommandStmt::RunFileStmt(_)))
            if message.starts_with("Failed to read file:") =>
        {
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

fn push_runtime_error_output_field_lines(
    runtime: &Runtime,
    field_lines: &mut Vec<String>,
    indent_inner: &str,
    output: &RuntimeErrorOutput,
) {
    if let Some(failed_step) = &output.failed_step {
        push_json_value_field_line(
            runtime,
            field_lines,
            indent_inner,
            JSON_KEY_FAILED_STEP,
            stmt_json_value(runtime, failed_step),
        );
    }
    if let Some(failed_goal) = &output.failed_goal {
        push_json_string_field_line(
            runtime,
            field_lines,
            indent_inner,
            JSON_KEY_FAILED_GOAL,
            &failed_goal.to_string(),
        );
    }
    if let Some(index) = output.proof_step_index {
        push_json_value_field_line(
            runtime,
            field_lines,
            indent_inner,
            "proof_step_index",
            JsonValue::Number(index),
        );
    }
    if let Some(count) = output.proof_step_count {
        push_json_value_field_line(
            runtime,
            field_lines,
            indent_inner,
            "proof_step_count",
            JsonValue::Number(count),
        );
    }
    if let Some(index) = output.then_clause_index {
        push_json_value_field_line(
            runtime,
            field_lines,
            indent_inner,
            "then_clause_index",
            JsonValue::Number(index),
        );
    }
    if let Some(count) = output.then_clause_count {
        push_json_value_field_line(
            runtime,
            field_lines,
            indent_inner,
            "then_clause_count",
            JsonValue::Number(count),
        );
    }
    if let Some(unknown_result) = &output.unknown_result {
        push_json_value_field_line(
            runtime,
            field_lines,
            indent_inner,
            JSON_KEY_UNKNOWN_RESULT,
            unknown_result_json_value(runtime, unknown_result),
        );
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

fn error_output(error: &RuntimeError) -> &RuntimeErrorOutput {
    match error {
        RuntimeError::DefineParamsError(e) => e.output.as_ref(),
        RuntimeError::NameAlreadyUsedError(e) => e.output.as_ref(),
        RuntimeError::ArithmeticError(e) => e.output.as_ref(),
        RuntimeError::NewFactError(e) => e.output.as_ref(),
        RuntimeError::StoreFactError(e) => e.output.as_ref(),
        RuntimeError::ParseError(e) => e.output.as_ref(),
        RuntimeError::ExecStmtError(e) => e.output.as_ref(),
        RuntimeError::WellDefinedError(e) => e.output.as_ref(),
        RuntimeError::VerifyError(e) => e.output.as_ref(),
        RuntimeError::UnknownError(e) => e.output.as_ref(),
        RuntimeError::InferError(e) => e.output.as_ref(),
        RuntimeError::InstantiateError(e) => e.output.as_ref(),
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

    push_runtime_error_output_field_lines(
        runtime,
        &mut field_lines,
        indent_inner.as_str(),
        error_output(error),
    );

    let context_for_child = error_own_statement(error).or(statement_context);
    let previous_error_line = build_previous_error_field_line(
        runtime,
        indent_inner.as_str(),
        error,
        depth + 1,
        include_previous_error,
        context_for_child,
    );
    if let Some(previous_error_line) = previous_error_line {
        field_lines.push(previous_error_line);
    }

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
) -> Option<String> {
    if !include_previous_error {
        if runtime.detail_output {
            return Some(format!(
                "{}\"{}\": null",
                indent_inner, JSON_KEY_PREVIOUS_ERROR
            ));
        }
        return None;
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
            Some(format!(
                "{}\"{}\":\n{}",
                indent_inner, JSON_KEY_PREVIOUS_ERROR, previous_error_json
            ))
        }
        None => {
            if runtime.detail_output {
                Some(format!(
                    "{}\"{}\": null",
                    indent_inner, JSON_KEY_PREVIOUS_ERROR
                ))
            } else {
                None
            }
        }
    }
}

fn get_previous_error_reference(error: &RuntimeError) -> Option<&RuntimeError> {
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
