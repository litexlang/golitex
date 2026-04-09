use crate::common::defaults::{is_default_line_file, LineFile};

/// Minimal JSON AST for pretty-printing (matches the previous `runtime_display_*` indentation style).
#[derive(Debug, Clone)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Number(usize),
    JsonString(String),
    Array(Vec<JsonValue>),
    Object(Vec<(String, JsonValue)>),
}

pub fn json_string_literal(source_text: &str) -> String {
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

pub fn json_one_level_indent(unit_count: usize) -> String {
    "  ".repeat(unit_count)
}

pub fn line_file_line_json_value(line_file: &LineFile) -> JsonValue {
    if is_default_line_file(line_file) {
        JsonValue::Null
    } else {
        JsonValue::Number(line_file.0)
    }
}

pub fn line_file_source_json_value(line_file: &LineFile) -> JsonValue {
    if is_default_line_file(line_file) {
        JsonValue::Null
    } else {
        JsonValue::JsonString(line_file.1.as_ref().to_string())
    }
}

fn render_json_primitive(v: &JsonValue) -> String {
    match v {
        JsonValue::Null => "null".to_string(),
        JsonValue::Bool(b) => b.to_string(),
        JsonValue::Number(n) => n.to_string(),
        JsonValue::JsonString(s) => json_string_literal(s),
        JsonValue::Array(_) | JsonValue::Object(_) => {
            unreachable!("render_json_primitive: non-primitive")
        }
    }
}

/// JSON fragment for `"line"`: `null` when [`is_default_line_file`], else the line number (unquoted).
pub fn line_file_line_json_fragment(line_file: &LineFile) -> String {
    render_json_primitive(&line_file_line_json_value(line_file))
}

/// JSON fragment for `"source"`: `null` when [`is_default_line_file`], else a quoted path string.
pub fn line_file_source_json_fragment(line_file: &LineFile) -> String {
    render_json_primitive(&line_file_source_json_value(line_file))
}

/// `depth` is the indent depth (number of two-space units) of the opening `{` of this object.
pub fn render_json_value(v: &JsonValue, depth: usize) -> String {
    match v {
        JsonValue::Object(fields) => {
            let indent_outer = json_one_level_indent(depth);
            let indent_inner = json_one_level_indent(depth + 1);
            let mut field_lines: Vec<String> = Vec::new();
            for (key, field_value) in fields.iter() {
                let line = match field_value {
                    JsonValue::Array(items) => {
                        if items.is_empty() {
                            format!("{}\"{}\": []", indent_inner, key)
                        } else {
                            let mut line = format!("{}\"{}\": [\n", indent_inner, key);
                            for (i, item) in items.iter().enumerate() {
                                if i > 0 {
                                    line.push_str(",\n");
                                }
                                match item {
                                    JsonValue::Object(_) => {
                                        line.push_str(&render_json_value(item, depth + 2));
                                    }
                                    _ => {
                                        line.push_str(&json_one_level_indent(depth + 2));
                                        line.push_str(&render_json_primitive(item));
                                    }
                                }
                            }
                            line.push('\n');
                            line.push_str(&indent_inner);
                            line.push(']');
                            line
                        }
                    }
                    JsonValue::Object(_) => {
                        format!(
                            "{}\"{}\": {}",
                            indent_inner,
                            key,
                            render_json_value(field_value, depth + 1)
                        )
                    }
                    _ => {
                        format!(
                            "{}\"{}\": {}",
                            indent_inner,
                            key,
                            render_json_primitive(field_value)
                        )
                    }
                };
                field_lines.push(line);
            }
            format!(
                "{}{{\n{}\n{}}}",
                indent_outer,
                field_lines.join(",\n"),
                indent_outer
            )
        }
        JsonValue::Array(_) => {
            unreachable!("render_json_value: Array only appears as object field value")
        }
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::JsonString(_) => {
            render_json_primitive(v)
        }
    }
}
