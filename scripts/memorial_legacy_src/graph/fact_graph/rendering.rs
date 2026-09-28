//! JSON summaries, longest chains, and Mermaid rendering.

use super::*;

impl FactGraphBuilder {
    pub(super) fn nodes_json(&self, include_source: bool) -> JsonValue {
        JsonValue::Array(
            self.nodes
                .iter()
                .map(|node| node.json_value(include_source))
                .collect(),
        )
    }

    pub(super) fn edges_json(&self) -> JsonValue {
        JsonValue::Array(self.edges.iter().map(FactGraphEdge::json_value).collect())
    }

    pub(super) fn summary_json(&self) -> JsonValue {
        let facts = self
            .nodes
            .iter()
            .filter(|node| {
                node.kind == "fact"
                    && node.fact_kind.as_deref() != Some("thm")
                    && node.fact_kind.as_deref() != Some("claim")
            })
            .count();
        let theorems = self
            .nodes
            .iter()
            .filter(|node| node.fact_kind.as_deref() == Some("thm"))
            .count();
        let claims = self
            .nodes
            .iter()
            .filter(|node| node.fact_kind.as_deref() == Some("claim"))
            .count();
        let trust_facts = self
            .nodes
            .iter()
            .filter(|node| node.fact_kind.as_deref() == Some("trust"))
            .count();
        let longest_chain = self.longest_chain();
        JsonValue::Object(vec![
            ("nodes".to_string(), JsonValue::Number(self.nodes.len())),
            ("edges".to_string(), JsonValue::Number(self.edges.len())),
            ("facts".to_string(), JsonValue::Number(facts)),
            ("theorems".to_string(), JsonValue::Number(theorems)),
            ("claims".to_string(), JsonValue::Number(claims)),
            ("trust_facts".to_string(), JsonValue::Number(trust_facts)),
            (
                "longest_chain_nodes".to_string(),
                JsonValue::Number(longest_chain.len()),
            ),
        ])
    }

    pub(super) fn empty_summary_json() -> JsonValue {
        JsonValue::Object(vec![
            ("nodes".to_string(), JsonValue::Number(0)),
            ("edges".to_string(), JsonValue::Number(0)),
            ("facts".to_string(), JsonValue::Number(0)),
            ("theorems".to_string(), JsonValue::Number(0)),
            ("claims".to_string(), JsonValue::Number(0)),
            ("trust_facts".to_string(), JsonValue::Number(0)),
            ("longest_chain_nodes".to_string(), JsonValue::Number(0)),
        ])
    }

    pub(super) fn longest_chain_json(&self) -> JsonValue {
        let node_ids = self.longest_chain();
        JsonValue::Object(vec![
            ("node_count".to_string(), JsonValue::Number(node_ids.len())),
            (
                "selection".to_string(),
                JsonValue::JsonString(
                    "facts, claims, and theorems; inferred facts are compressed into edges"
                        .to_string(),
                ),
            ),
            (
                "node_ids".to_string(),
                JsonValue::Array(node_ids.into_iter().map(JsonValue::JsonString).collect()),
            ),
        ])
    }

    pub(super) fn empty_longest_chain_json() -> JsonValue {
        JsonValue::Object(vec![
            ("node_count".to_string(), JsonValue::Number(0)),
            (
                "selection".to_string(),
                JsonValue::JsonString(
                    "facts, claims, and theorems; inferred facts are compressed into edges"
                        .to_string(),
                ),
            ),
            ("node_ids".to_string(), JsonValue::Array(vec![])),
        ])
    }

    pub(super) fn longest_chain(&self) -> Vec<String> {
        let mut outgoing: HashMap<String, Vec<String>> = HashMap::new();
        for edge in &self.edges {
            let Some(from_index) = self.node_index.get(&edge.from).copied() else {
                continue;
            };
            let Some(to_index) = self.node_index.get(&edge.to).copied() else {
                continue;
            };
            if !fact_graph_node_belongs_to_main_chain(&self.nodes[from_index])
                || !fact_graph_node_belongs_to_main_chain(&self.nodes[to_index])
            {
                continue;
            }
            outgoing
                .entry(edge.from.clone())
                .or_default()
                .push(edge.to.clone());
        }
        let mut memo = HashMap::new();
        let mut visiting = HashSet::new();
        let mut longest = vec![];
        for node in &self.nodes {
            if !fact_graph_node_belongs_to_main_chain(node) {
                continue;
            }
            let candidate =
                longest_chain_from(node.id.as_str(), &outgoing, &mut memo, &mut visiting);
            if candidate.len() > longest.len() {
                longest = candidate;
            }
        }
        longest
    }

    pub(super) fn mermaid(&self) -> String {
        let mut lines = vec!["flowchart LR".to_string()];
        for node in &self.nodes {
            lines.push(format!(
                "    {}{}",
                mermaid_id(&node.id),
                mermaid_node_shape(node)
            ));
        }
        for edge in &self.edges {
            let label = if edge.count > 1 {
                format!("{} x{}", edge.kind, edge.count)
            } else {
                edge.kind.clone()
            };
            lines.push(format!(
                "    {} -->|{}| {}",
                mermaid_id(&edge.from),
                label,
                mermaid_id(&edge.to)
            ));
        }
        lines.join("\n")
    }
}
