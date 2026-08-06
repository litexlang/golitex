use crate::prelude::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CurrentJsonProofRoute {
    Calculation,
    RationalExpressionSimplification,
}

impl CurrentJsonProofRoute {
    pub fn output_label(self) -> &'static str {
        match self {
            CurrentJsonProofRoute::Calculation => "calculation",
            CurrentJsonProofRoute::RationalExpressionSimplification => {
                "rational expression simplification"
            }
        }
    }
}

pub(super) fn statement_and_route_from_current_json(
    json: &str,
) -> Result<(String, CurrentJsonProofRoute), RuntimeError> {
    let result = json_string_field(json, "result")?;
    if result != "success" {
        return Err(current_json_error(
            "To-Lean requires a successful Litex statement JSON object",
        ));
    }

    let statement = json_string_field(json, "statement")?;
    let rule = json_string_field(json, "rule")?;
    let route = match rule.as_str() {
        "calculation" | "direct numeric computation" => CurrentJsonProofRoute::Calculation,
        "bounded symbolic normalization" | "calculation and rational expression simplification" => {
            CurrentJsonProofRoute::RationalExpressionSimplification
        }
        _ => {
            return Err(current_json_error(format!(
                "To-Lean current-JSON adapter does not support verification rule `{}`",
                rule
            )))
        }
    };
    Ok((statement, route))
}

fn json_string_field(json: &str, field: &str) -> Result<String, RuntimeError> {
    let marker = format!("\"{}\"", field);
    let Some(marker_start) = json.find(marker.as_str()) else {
        return Err(current_json_error(format!(
            "To-Lean current-JSON adapter could not find `{}`",
            field
        )));
    };
    let after_marker = &json[marker_start + marker.len()..];
    let Some(colon_offset) = after_marker.find(':') else {
        return Err(current_json_error(format!(
            "To-Lean current-JSON adapter found malformed `{}`",
            field
        )));
    };
    let value = after_marker[colon_offset + 1..].trim_start();
    if !value.starts_with('"') {
        return Err(current_json_error(format!(
            "To-Lean current-JSON adapter requires string field `{}`",
            field
        )));
    }
    decode_json_string(value, field)
}

fn decode_json_string(value: &str, field: &str) -> Result<String, RuntimeError> {
    let mut output = String::new();
    let mut characters = value[1..].chars();
    while let Some(character) = characters.next() {
        match character {
            '"' => return Ok(output),
            '\\' => {
                let Some(escaped) = characters.next() else {
                    return Err(current_json_error(format!(
                        "To-Lean current-JSON adapter found an incomplete escape in `{}`",
                        field
                    )));
                };
                match escaped {
                    '"' => output.push('"'),
                    '\\' => output.push('\\'),
                    '/' => output.push('/'),
                    'b' => output.push('\u{0008}'),
                    'f' => output.push('\u{000c}'),
                    'n' => output.push('\n'),
                    'r' => output.push('\r'),
                    't' => output.push('\t'),
                    'u' => {
                        let mut digits = String::new();
                        for _ in 0..4 {
                            let Some(digit) = characters.next() else {
                                return Err(current_json_error(format!(
                                    "To-Lean current-JSON adapter found an incomplete Unicode escape in `{}`",
                                    field
                                )));
                            };
                            digits.push(digit);
                        }
                        let codepoint = u32::from_str_radix(digits.as_str(), 16).map_err(|_| {
                            current_json_error(format!(
                                "To-Lean current-JSON adapter found an invalid Unicode escape in `{}`",
                                field
                            ))
                        })?;
                        let decoded = char::from_u32(codepoint).ok_or_else(|| {
                            current_json_error(format!(
                                "To-Lean current-JSON adapter found an invalid Unicode codepoint in `{}`",
                                field
                            ))
                        })?;
                        output.push(decoded);
                    }
                    _ => {
                        return Err(current_json_error(format!(
                            "To-Lean current-JSON adapter found an unsupported escape in `{}`",
                            field
                        )))
                    }
                }
            }
            control if control.is_control() => {
                return Err(current_json_error(format!(
                    "To-Lean current-JSON adapter found an unescaped control character in `{}`",
                    field
                )))
            }
            other => output.push(other),
        }
    }
    Err(current_json_error(format!(
        "To-Lean current-JSON adapter found an unterminated string in `{}`",
        field
    )))
}

fn current_json_error(message: impl Into<String>) -> RuntimeError {
    UnknownRuntimeError(RuntimeErrorStruct::new(
        None,
        message.into(),
        default_line_file(),
        None,
        vec![],
    ))
    .into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extracts_multiline_statement_and_rational_route() {
        let json = r#"{
  "result": "success",
  "statement": "forall x R:\n    x = x",
  "why_verified": {
    "rule": "bounded symbolic normalization"
  }
}"#;
        let (statement, route) = statement_and_route_from_current_json(json).unwrap();
        assert_eq!(statement, "forall x R:\n    x = x");
        assert_eq!(
            route,
            CurrentJsonProofRoute::RationalExpressionSimplification
        );
    }

    #[test]
    fn rejects_a_success_without_supported_rule_output() {
        let json = r#"{
  "result": "success",
  "statement": "a = c",
  "why_verified": {
    "rule": "same known equality class"
  }
}"#;
        let error = statement_and_route_from_current_json(json)
            .expect_err("known equality is outside this JSON adapter")
            .trace_message();
        assert!(error.contains("does not support verification rule"));
    }
}
