//! Definition graph node JSON encoding.

use super::*;

impl DefinitionGraphNode {
    pub(super) fn json_value(&self, include_source: bool) -> JsonValue {
        let mut fields = vec![
            ("id".to_string(), JsonValue::JsonString(self.id.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            (
                "definition_kind".to_string(),
                JsonValue::JsonString(self.definition_kind.clone()),
            ),
            ("name".to_string(), JsonValue::JsonString(self.name.clone())),
            (
                "label".to_string(),
                JsonValue::JsonString(self.label.clone()),
            ),
            ("defined".to_string(), JsonValue::Bool(self.defined)),
            (
                "semantic_role".to_string(),
                JsonValue::JsonString(self.semantic_role.clone()),
            ),
            (
                "litex_form".to_string(),
                JsonValue::JsonString(self.litex_form.clone()),
            ),
            (
                "knowledge_status".to_string(),
                JsonValue::JsonString(self.knowledge_status.clone()),
            ),
            (
                "trust_kind".to_string(),
                self.trust_kind
                    .as_ref()
                    .map(|kind| JsonValue::JsonString(kind.clone()))
                    .unwrap_or(JsonValue::Null),
            ),
        ];
        if let Some(line_file) = self.line_file.as_ref() {
            fields.push(("line".to_string(), JsonValue::Number(line_file.0)));
        }
        if include_source {
            if let Some(statement) = self.statement.as_ref() {
                fields.push((
                    "statement".to_string(),
                    JsonValue::JsonString(statement.clone()),
                ));
            }
        }
        JsonValue::Object(fields)
    }
}
