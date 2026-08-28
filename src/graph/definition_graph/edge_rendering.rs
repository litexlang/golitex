//! Definition graph edge JSON encoding.

use super::*;

impl DefinitionGraphEdge {
    pub(super) fn json_value(&self) -> JsonValue {
        JsonValue::Object(vec![
            ("from".to_string(), JsonValue::JsonString(self.from.clone())),
            ("to".to_string(), JsonValue::JsonString(self.to.clone())),
            ("kind".to_string(), JsonValue::JsonString(self.kind.clone())),
            (
                "referenced_kind".to_string(),
                JsonValue::JsonString(self.reference_kind.clone()),
            ),
            (
                "reference_kind".to_string(),
                JsonValue::JsonString(self.reference_kind.clone()),
            ),
            ("count".to_string(), JsonValue::Number(self.count)),
        ])
    }
}
