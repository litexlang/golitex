//! Fact graph node JSON encoding.

use super::*;

impl FactGraphNode {
    pub(super) fn json_value(&self, include_source: bool) -> JsonValue {
        let mut fields = vec![
            ("id".to_string(), JsonValue::JsonString(self.id.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            (
                "label".to_string(),
                JsonValue::JsonString(self.label.clone()),
            ),
            ("defined".to_string(), JsonValue::Bool(true)),
        ];
        if let Some(fact_kind) = &self.fact_kind {
            fields.push((
                "fact_kind".to_string(),
                JsonValue::JsonString(fact_kind.clone()),
            ));
        }
        if let Some(line_file) = &self.line_file {
            fields.push(("line".to_string(), fact_graph_line_json_value(line_file)));
            if include_source && !is_default_line_file(line_file) {
                fields.push((
                    "source".to_string(),
                    JsonValue::JsonString(line_file.1.as_ref().to_string()),
                ));
            }
        }
        if let Some(statement) = &self.statement {
            fields.push((
                "statement".to_string(),
                JsonValue::JsonString(strip_free_param_numeric_tags_in_display(statement)),
            ));
        }
        if let Some(reason) = &self.reason {
            fields.push((
                "store_reason".to_string(),
                JsonValue::JsonString(reason.clone()),
            ));
        }
        JsonValue::Object(fields)
    }
}
