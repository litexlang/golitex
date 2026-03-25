use super::RuntimeContext;
use crate::common::defaults::DEFAULT_LINE_FILE;
use crate::common::keywords::{COLON, PROVE};
use crate::error::{duplicate_used_name_error_message, ParseBlockError, RuntimeError};
use crate::result::NonErrStmtExecResult;
use crate::stmt::Stmt;

const JSON_KEY_ERROR_TYPE: &str = "error_type";
const JSON_KEY_RESULT: &str = "result";
const JSON_KEY_MESSAGE: &str = "message";
const JSON_KEY_LINE: &str = "line";
const JSON_KEY_SOURCE: &str = "source";
const JSON_KEY_STMT_TYPE: &str = "stmt_type";
const JSON_KEY_STMT: &str = "stmt";
const JSON_KEY_INSIDE_RESULTS: &str = "inside_results";
const JSON_KEY_PREVIOUS_ERROR: &str = "previous_error";
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

fn parse_block_error_message(parse_block_error: &ParseBlockError) -> String {
    match parse_block_error {
        ParseBlockError::ExpectedIndent(_, _) => "expected indent".to_string(),
        ParseBlockError::UnexpectedIndent(_, _) => "unexpected indent".to_string(),
        ParseBlockError::InconsistentIndent(_, _) => "inconsistent indent".to_string(),
        ParseBlockError::MissingBody(_, _) => "block header missing body".to_string(),
        ParseBlockError::NameAlreadyUsed(name) => duplicate_used_name_error_message(name),
        ParseBlockError::InvalidName(msg) => msg.clone(),
    }
}

impl<'a> RuntimeContext<'a> {
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
            indent_inner, JSON_KEY_ERROR_TYPE, json_string_literal(error.display_label())
        ));
        field_lines.push(format!(
            "{}\"{}\": {}",
            indent_inner, JSON_KEY_RESULT, json_string_literal(JSON_VALUE_ERROR)
        ));

        let (line, file_index) = error.line_file();
        field_lines.push(format!("{}\"{}\": {}", indent_inner, JSON_KEY_LINE, line));
        let source_text = match self.module_manager.run_file_paths.get(file_index) {
            Some(source_path) => source_path.as_str(),
            None => "",
        };
        // Keep `source` empty when line/file are default to avoid misleading info.
        if (line, file_index) == DEFAULT_LINE_FILE {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner, JSON_KEY_SOURCE, json_string_literal("")
            ));
        } else {
            field_lines.push(format!(
                "{}\"{}\": {}",
                indent_inner, JSON_KEY_SOURCE, json_string_literal(source_text)
            ));
        }

        match error {
            RuntimeError::ArithmeticError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::NewAtomicFactError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::StoreFactError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::ParseBlockError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&parse_block_error_message(e))
                ));
            }
            RuntimeError::ParsingError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.msg)
                ));
            }
            RuntimeError::ExecStmtError(e) => {
                let stmt_display_string = e.stmt.to_string();
                let wrapped_stmt_display_string = match &e.stmt {
                    Stmt::ProveStmt(_) => format!("{}{}\n{}", PROVE, COLON, stmt_display_string),
                    _ => stmt_display_string,
                };
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_STMT_TYPE,
                    json_string_literal(e.stmt.stmt_type_name().as_str())
                ));
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner, JSON_KEY_STMT, json_string_literal(&wrapped_stmt_display_string)
                ));

                let mut inside_result_elements: Vec<String> = Vec::new();
                for inside_result in e.inside_results.iter() {
                    inside_result_elements.push(
                        self.runtime_context_display_result_json_string(inside_result),
                    );
                }
                field_lines.push(json_array_field_line(
                    indent_inner.as_str(),
                    JSON_KEY_INSIDE_RESULTS,
                    &inside_result_elements,
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
                    json_string_literal(&e.fact.to_string())
                ));
            }
            RuntimeError::VerifyUnknownError(e) => {
                field_lines.push(format!(
                    "{}\"{}\": {}",
                    indent_inner,
                    JSON_KEY_MESSAGE,
                    json_string_literal(&e.fact.to_string())
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
                let previous_error_json =
                    self.build_display_error_json_object(previous_error, previous_error_depth, false);
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
            RuntimeError::ParseBlockError(_) => None,
            RuntimeError::ParsingError(e) => match &e.previous_error {
                Some(previous_error) => Some(previous_error.as_ref()),
                None => None,
            },
            RuntimeError::ExecStmtError(e) => match &e.previous_error {
                Some(previous_error) => Some(previous_error.as_ref()),
                None => None,
            },
            RuntimeError::UnknownError(e) => match &e.previous_error {
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
            RuntimeError::VerifyUnknownError(e) => match &e.previous_error {
                Some(previous_error) => Some(previous_error.as_ref()),
                None => None,
            },
            RuntimeError::InferError(e) => match &e.previous_error {
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
}