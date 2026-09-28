//! Summary, JSON, and Mermaid rendering.

use super::*;

impl ResultGraph {
    pub fn summary_json(&self) -> JsonValue {
        JsonValue::Object(vec![
            ("nodes".to_string(), JsonValue::Number(self.nodes.len())),
            ("edges".to_string(), JsonValue::Number(self.edges.len())),
            (
                "statements".to_string(),
                JsonValue::Number(self.count_kind("statement")),
            ),
            (
                "verifications".to_string(),
                JsonValue::Number(self.count_kind("verification")),
            ),
            (
                "well_definedness".to_string(),
                JsonValue::Number(self.count_kind("well_definedness")),
            ),
            (
                "proofs".to_string(),
                JsonValue::Number(self.count_kind("proof")),
            ),
            (
                "stores".to_string(),
                JsonValue::Number(self.count_kind("store") + self.count_kind("store_effect")),
            ),
            (
                "facts".to_string(),
                JsonValue::Number(self.count_kind("fact")),
            ),
            (
                "inferences".to_string(),
                JsonValue::Number(self.count_kind("inference")),
            ),
            (
                "unknowns".to_string(),
                JsonValue::Number(self.count_kind("unknown")),
            ),
        ])
    }

    pub(super) fn count_kind(&self, kind: &str) -> usize {
        self.nodes.iter().filter(|node| node.kind == kind).count()
    }

    pub fn nodes_json(&self) -> JsonValue {
        JsonValue::Array(
            self.nodes
                .iter()
                .map(|node| {
                    JsonValue::Object(vec![
                        ("id".to_string(), JsonValue::JsonString(node.id.clone())),
                        ("kind".to_string(), JsonValue::JsonString(node.kind.clone())),
                        ("role".to_string(), JsonValue::JsonString(node.role.clone())),
                        (
                            "label".to_string(),
                            JsonValue::JsonString(node.label.clone()),
                        ),
                        (
                            "fact_id".to_string(),
                            node.fact_id
                                .map(|id| JsonValue::JsonString(id.to_string()))
                                .unwrap_or(JsonValue::Null),
                        ),
                    ])
                })
                .collect(),
        )
    }

    pub fn edges_json(&self) -> JsonValue {
        JsonValue::Array(
            self.edges
                .iter()
                .map(|edge| {
                    JsonValue::Object(vec![
                        ("from".to_string(), JsonValue::JsonString(edge.from.clone())),
                        ("to".to_string(), JsonValue::JsonString(edge.to.clone())),
                        ("kind".to_string(), JsonValue::JsonString(edge.kind.clone())),
                        ("order".to_string(), JsonValue::Number(edge.order)),
                    ])
                })
                .collect(),
        )
    }

    pub fn mermaid(&self) -> String {
        let mut lines = vec!["flowchart LR".to_string()];
        for (index, node) in self.nodes.iter().enumerate() {
            lines.push(format!(
                "  n{index}[\"{}: {}\"]",
                mermaid_label(&node.role),
                mermaid_label(&node.label)
            ));
        }
        for edge in self.edges.iter() {
            let Some(from) = self.node_index.get(&edge.from) else {
                continue;
            };
            let Some(to) = self.node_index.get(&edge.to) else {
                continue;
            };
            lines.push(format!(
                "  n{from} -->|{}| n{to}",
                mermaid_label(&edge.kind)
            ));
        }
        lines.join("\n")
    }
}
