use crate::prelude::*;

const JSON_KEY_ERROR_TYPE: &str = "error_type";
const JSON_KEY_RESULT: &str = "result";
const JSON_KEY_MESSAGE: &str = "message";
const JSON_KEY_LINE: &str = "line";
const JSON_KEY_SOURCE: &str = "source";
const JSON_KEY_STMT_TYPE: &str = "stmt_type";
const JSON_KEY_STMT: &str = "stmt";
const JSON_KEY_INSIDE_RESULTS: &str = "inside_results";
const JSON_KEY_PREVIOUS_ERROR: &str = "previous_error";
const JSON_KEY_CONFLICT_WITH: &str = "conflict_with";
const JSON_VALUE_ERROR: &str = "error";

fn json_one_level_indent(unit_count: usize) -> String {
    let mut indent = String::new();
    for _ in 0..unit_count {
        indent.push_str("  ");
    }
    indent
}

fn json_string_literal(source_text: &str) -> String {
    let mut output = String::with_capacity(source_text.len() + 2);
    output.push('"');
    for ch in source_text.chars() {
        match ch {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            c if (c as u32) < 32 => {
                output.push_str(format!("\\u{:04x}", c as u32).as_str());
            }
            c => output.push(c),
        }
    }
    output.push('"');
    output
}

fn json_array_field_line(
    indent_inner: &str,
    json_key: &str,
    json_elements: &Vec<String>,
) -> String {
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
    let stmt_display_string = stmt.to_string();
    let wrapped_stmt_display_string = match stmt {
        Stmt::ProveStmt(_) => format!("{}{}\n{}", PROVE, COLON, stmt_display_string),
        _ => stmt_display_string,
    };
    let mut lines: Vec<String> = Vec::new();
    lines.push(format!(
        "{}\"{}\": {}",
        indent_inner,
        JSON_KEY_STMT_TYPE,
        json_string_literal(stmt.stmt_type_name().as_str())
    ));
    lines.push(format!(
        "{}\"{}\": {}",
        indent_inner,
        JSON_KEY_STMT,
        json_string_literal(&wrapped_stmt_display_string)
    ));
    lines
}

fn push_optional_conflict_with_json_field_lines(
    runtime: &Runtime,
    field_lines: &mut Vec<String>,
    indent_inner: &str,
    conflict_with: &Option<ConflictMsg>,
) {
    match conflict_with {
        None => field_lines.push(format!(
            "{}\"{}\": null",
            indent_inner, JSON_KEY_CONFLICT_WITH
        )),
        Some(conflict) => {
            let indent_nested = format!("{}  ", indent_inner);
            let conflict_line_file = conflict.line_file.clone();
            let conflict_line = conflict_line_file.0;
            let conflict_source = runtime.get_file_name_empty_if_default(conflict_line_file);
            let message_literal = json_string_literal(&conflict.msg);
            let source_literal = json_string_literal(conflict_source.as_str());
            let mut inner_lines: Vec<String> = Vec::new();
            inner_lines.push(format!(
                "{}\"{}\": {}",
                indent_nested,
                JSON_KEY_MESSAGE,
                message_literal
            ));
            inner_lines.push(format!(
                "{}\"{}\": {}",
                indent_nested,
                JSON_KEY_LINE,
                conflict_line
            ));
            inner_lines.push(format!(
                "{}\"{}\": {}",
                indent_nested,
                JSON_KEY_SOURCE,
                source_literal
            ));
            push_optional_statement_json_field_lines(
                &mut inner_lines,
                indent_nested.as_str(),
                &conflict.stmt,
            );
            field_lines.push(format!(
                "{}\"{}\": {{\n{}\n{}}}",
                indent_inner,
                JSON_KEY_CONFLICT_WITH,
                inner_lines.join(",\n"),
                indent_inner,
            ));
        }
    }
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

impl Runtime {
    pub fn display_error_json_string(&self, error: &RuntimeError) -> String {
        self.build_display_error_json_object(error, 0, true)
    }

    fn build_display_error_json_object(
        &self,
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
        let line = line_file.0;
        field_lines.push(format!("{}\"{}\": {}", indent_inner, JSON_KEY_LINE, line));

        let source_text = self.get_file_name_empty_if_default(line_file.clone());

        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner,
            JSON_KEY_SOURCE,
            json_string_literal(source_text.as_str())
        ));

        match error {
            RuntimeError::DefineParamsError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::NameAlreadyUsedError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::ArithmeticError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
                push_optional_statement_json_field_lines(
                    &mut field_lines,
                    indent_inner.as_str(),
                    &e.statement,
                );
                push_optional_conflict_with_json_field_lines(
                    self,
                    &mut field_lines,
                    indent_inner.as_str(),
                    &e.conflict_with,
                );
            }
            RuntimeError::NewAtomicFactError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
                push_optional_statement_json_field_lines(
                    &mut field_lines,
                    indent_inner.as_str(),
                    &e.statement,
                );
                push_optional_conflict_with_json_field_lines(
                    self,
                    &mut field_lines,
                    indent_inner.as_str(),
                    &e.conflict_with,
                );
            }
            RuntimeError::StoreFactError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
                push_optional_statement_json_field_lines(
                    &mut field_lines,
                    indent_inner.as_str(),
                    &e.statement,
                );
                push_optional_conflict_with_json_field_lines(
                    self,
                    &mut field_lines,
                    indent_inner.as_str(),
                    &e.conflict_with,
                );
            }
            RuntimeError::ParseError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::ExecStmtError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
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
                        .push(self.runtime_context_display_result_json_string(inside_result));
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
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::VerifyError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::UnknownError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::InferError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::InstantiateError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
                push_optional_statement_json_field_lines(
                    &mut field_lines,
                    indent_inner.as_str(),
                    &e.statement,
                );
                push_optional_conflict_with_json_field_lines(
                    self,
                    &mut field_lines,
                    indent_inner.as_str(),
                    &e.conflict_with,
                );
            }
        }

        let previous_error_line = self.build_previous_error_field_line(
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
        &self,
        indent_inner: &str,
        error: &RuntimeError,
        previous_error_depth: usize,
        include_previous_error: bool,
    ) -> String {
        if !include_previous_error {
            return format!("{}\"{}\": null", indent_inner, JSON_KEY_PREVIOUS_ERROR);
        }

        let previous_error_reference = self.get_previous_error_reference(error);
        match previous_error_reference {
            Some(previous_error) => {
                let previous_error_json = self.build_display_error_json_object(
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

    fn get_previous_error_reference<'b>(
        &self,
        error: &'b RuntimeError,
    ) -> Option<&'b RuntimeError> {
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
            RuntimeError::NewAtomicFactError(e) => match &e.previous_error {
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

    fn runtime_context_display_result_json_string(
        &self,
        inside_result: &NonErrStmtExecResult,
    ) -> String {
        // We reuse the existing json result formatter for nested results.
        self.display_result_json_string(inside_result)
    }

    pub(in crate::runtime) fn get_file_name_empty_if_default(&self, line_file: LineFile) -> String {
        if is_default_line_file(&line_file) {
            return String::new();
        }
        line_file.1.as_ref().to_string()
    }
}
