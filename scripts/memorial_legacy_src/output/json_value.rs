use crate::syntax::source_conventions::{is_default_line_file, LineFile};

/// Minimal JSON AST for pretty-printing (matches the previous `runtime_display_*` indentation style).
#[derive(Debug, Clone)]
pub enum JsonValue {
    Null,
    Bool(bool),
    Number(usize),
    JsonString(String),
    RawJson(String),
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

pub fn run_target_json_value(
    target_kind: &str,
    target_path: Option<&str>,
    hide_file_paths: bool,
) -> JsonValue {
    let mut fields = vec![(
        "kind".to_string(),
        JsonValue::JsonString(target_kind.to_string()),
    )];
    if !hide_file_paths {
        if let Some(path) = target_path {
            fields.push(("path".to_string(), JsonValue::JsonString(path.to_string())));
        }
    }
    JsonValue::Object(fields)
}

fn render_json_primitive(v: &JsonValue) -> String {
    match v {
        JsonValue::Null => "null".to_string(),
        JsonValue::Bool(b) => b.to_string(),
        JsonValue::Number(n) => n.to_string(),
        JsonValue::JsonString(s) => json_string_literal(s),
        JsonValue::RawJson(_) | JsonValue::Array(_) | JsonValue::Object(_) => {
            unreachable!("render_json_primitive: non-primitive")
        }
    }
}

fn render_raw_json(source: &str, depth: usize) -> String {
    let indent = json_one_level_indent(depth);
    source
        .trim()
        .lines()
        .map(|line| format!("{}{}", indent, line))
        .collect::<Vec<_>>()
        .join("\n")
}

/// JSON fragment for `"line"`: `null` when [`is_default_line_file`], else the line number (unquoted).
pub fn line_file_line_json_fragment(line_file: &LineFile) -> String {
    render_json_primitive(&line_file_line_json_value(line_file))
}

/// JSON fragment for `"source"`: `null` when [`is_default_line_file`], else a quoted path string.
pub fn line_file_source_json_fragment(line_file: &LineFile) -> String {
    render_json_primitive(&line_file_source_json_value(line_file))
}

fn render_json_array(items: &[JsonValue], depth: usize) -> String {
    let indent_outer = json_one_level_indent(depth);
    let indent_inner = json_one_level_indent(depth + 1);
    if items.is_empty() {
        return "[]".to_string();
    }

    let mut output = String::from("[\n");
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            output.push_str(",\n");
        }
        match item {
            JsonValue::Object(_) => output.push_str(&render_json_value(item, depth + 1)),
            JsonValue::Array(nested_items) => {
                output.push_str(&indent_inner);
                output.push_str(&render_json_array(nested_items, depth + 1));
            }
            JsonValue::RawJson(source) => {
                output.push_str(&render_raw_json(source, depth + 1));
            }
            _ => {
                output.push_str(&indent_inner);
                output.push_str(&render_json_primitive(item));
            }
        }
    }
    output.push('\n');
    output.push_str(&indent_outer);
    output.push(']');
    output
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
                            format!(
                                "{}\"{}\": {}",
                                indent_inner,
                                key,
                                render_json_array(items, depth + 1)
                            )
                        }
                    }
                    JsonValue::Object(_) => {
                        let rendered = render_json_value(field_value, depth + 1);
                        let rendered = rendered
                            .strip_prefix(indent_inner.as_str())
                            .unwrap_or(rendered.as_str());
                        format!("{}\"{}\": {}", indent_inner, key, rendered)
                    }
                    JsonValue::RawJson(source) => {
                        let rendered = render_raw_json(source, depth + 1);
                        let rendered = rendered
                            .strip_prefix(indent_inner.as_str())
                            .unwrap_or(rendered.as_str());
                        format!("{}\"{}\": {}", indent_inner, key, rendered)
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
        JsonValue::RawJson(source) => render_raw_json(source, depth),
        JsonValue::Null | JsonValue::Bool(_) | JsonValue::Number(_) | JsonValue::JsonString(_) => {
            render_json_primitive(v)
        }
    }
}

pub fn render_json_value_compact(value: &JsonValue) -> String {
    match value {
        JsonValue::Null => "null".to_string(),
        JsonValue::Bool(value) => value.to_string(),
        JsonValue::Number(value) => value.to_string(),
        JsonValue::JsonString(value) => json_string_literal(value),
        JsonValue::RawJson(value) => compact_raw_json(value),
        JsonValue::Array(items) => format!(
            "[{}]",
            items
                .iter()
                .map(render_json_value_compact)
                .collect::<Vec<_>>()
                .join(",")
        ),
        JsonValue::Object(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(key, value)| format!(
                    "{}:{}",
                    json_string_literal(key),
                    render_json_value_compact(value)
                ))
                .collect::<Vec<_>>()
                .join(",")
        ),
    }
}

fn compact_raw_json(source: &str) -> String {
    let mut output = String::with_capacity(source.len());
    let mut inside_string = false;
    let mut escaped = false;
    for character in source.trim().chars() {
        if inside_string {
            output.push(character);
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                inside_string = false;
            }
        } else if character == '"' {
            inside_string = true;
            output.push(character);
        } else if !character.is_whitespace() {
            output.push(character);
        }
    }
    output
}
