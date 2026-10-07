use super::helper::{object, string};
use super::math_graph::MathGraph;
use crate::knowledge_base::JsonValue;

impl MathGraph {
    pub fn json(&self, success: bool, target: &str, path: Option<&str>) -> String {
        let nodes = self.nodes.iter().map(|n| object(vec![
            ("id", string(&n.id)), ("kind", string(&n.kind)),
            ("name", n.name.as_ref().map(|s| string(s)).unwrap_or(JsonValue::Null)),
            ("label", string(&n.label)), ("statement", string(&n.statement)),
            ("source", string(&n.source)), ("line", n.line.map(|i| JsonValue::Number(i as f64)).unwrap_or(JsonValue::Null)),
            ("scope", string(&n.scope)), ("origin", string(&n.origin)),
            ("inferred", JsonValue::Bool(n.inferred)), ("published", JsonValue::Bool(n.published)),
            ("history_available", JsonValue::Bool(n.history_available)),
            ("default_visible", JsonValue::Bool(!n.inferred && !n.scope.starts_with("local:"))),
        ])).collect();
        let edges = self.edges.iter().map(|e| object(vec![
            ("from", string(&e.from)), ("to", string(&e.to)), ("kind", string(&e.kind)),
            ("dependency_group", JsonValue::Number(e.group as f64)),
            ("statement", string(&e.statement)), ("source", string(&e.source)),
        ])).collect();
        object(vec![
            ("kind", string("math_graph")), ("schema_version", JsonValue::Number(1.0)),
            ("success", JsonValue::Bool(success)), ("partial", JsonValue::Bool(!success && !self.nodes.is_empty())),
            ("target", string(target)), ("path", path.map(string).unwrap_or(JsonValue::Null)),
            ("language", string(self.language.as_str())), ("nodes", JsonValue::Array(nodes)),
            ("edges", JsonValue::Array(edges)), ("diagnostics", JsonValue::Array(self.diagnostics.clone())),
            ("mermaid", string(self.mermaid())),
        ]).stringify_pretty()
    }

    fn mermaid(&self) -> String {
        let mut result = "flowchart LR\n".to_string();
        let mut visible = std::collections::HashSet::new();
        for (index, node) in self.nodes.iter().enumerate() {
            if node.inferred || node.scope.starts_with("local:") { continue; }
            visible.insert(node.id.clone());
            let label = node.label.replace('&', "&amp;").replace('"', "&quot;").replace('<', "&lt;").replace('>', "&gt;").replace('\n', "<br/>");
            result.push_str(&format!("  n{index}[\"{label}\"]\n"));
        }
        for edge in &self.edges {
            if visible.contains(&edge.from) && visible.contains(&edge.to) {
                if let (Some(left), Some(right)) = (self.node_index.get(&edge.from), self.node_index.get(&edge.to)) {
                    result.push_str(&format!("  n{left} -->|{}| n{right}\n", edge.kind));
                }
            }
        }
        result
    }
}
