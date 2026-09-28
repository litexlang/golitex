//! JSON summaries, DAG topology, cycles, and Mermaid rendering.

use super::*;

impl DefinitionGraphBuilder {
    pub(super) fn nodes_json(&self, include_source: bool) -> JsonValue {
        JsonValue::Array(
            self.nodes
                .iter()
                .map(|node| node.json_value(include_source))
                .collect(),
        )
    }

    pub(super) fn edges_json(&self) -> JsonValue {
        JsonValue::Array(
            self.edges
                .iter()
                .map(DefinitionGraphEdge::json_value)
                .collect(),
        )
    }

    pub(super) fn summary_json(&self) -> JsonValue {
        let mut kinds = HashMap::<String, usize>::new();
        let mut edge_kinds = HashMap::<String, usize>::new();
        let mut knowledge_statuses = HashMap::<String, usize>::new();
        let mut defined_nodes = 0;
        for node in &self.nodes {
            if node.defined {
                defined_nodes += 1;
            }
            *kinds.entry(node.definition_kind.clone()).or_insert(0) += 1;
            *knowledge_statuses
                .entry(node.knowledge_status.clone())
                .or_insert(0) += 1;
        }
        for edge in &self.edges {
            *edge_kinds.entry(edge.kind.clone()).or_insert(0) += edge.count;
        }
        let edge_kind_counts = sorted_count_object(edge_kinds);
        let knowledge_status_counts = sorted_count_object(knowledge_statuses);
        let mut fields = vec![
            ("nodes".to_string(), JsonValue::Number(self.nodes.len())),
            (
                "defined_nodes".to_string(),
                JsonValue::Number(defined_nodes),
            ),
            ("edges".to_string(), JsonValue::Number(self.edges.len())),
            (
                "edge_uses".to_string(),
                JsonValue::Number(self.edges.iter().map(|edge| edge.count).sum()),
            ),
            ("is_dag".to_string(), JsonValue::Bool(self.is_dag())),
            (
                "topological_nodes".to_string(),
                JsonValue::Number(self.topological_order().len()),
            ),
            (
                "cycle_nodes".to_string(),
                JsonValue::Number(self.cycle_nodes().len()),
            ),
            ("edge_kinds".to_string(), edge_kind_counts),
            ("knowledge_statuses".to_string(), knowledge_status_counts),
        ];
        let mut kinds = kinds.into_iter().collect::<Vec<_>>();
        kinds.sort_by(|left, right| left.0.cmp(&right.0));
        for (kind, count) in kinds {
            fields.push((kind, JsonValue::Number(count)));
        }
        JsonValue::Object(fields)
    }

    pub(super) fn empty_summary_json() -> JsonValue {
        JsonValue::Object(vec![
            ("nodes".to_string(), JsonValue::Number(0)),
            ("defined_nodes".to_string(), JsonValue::Number(0)),
            ("edges".to_string(), JsonValue::Number(0)),
            ("edge_uses".to_string(), JsonValue::Number(0)),
            ("is_dag".to_string(), JsonValue::Bool(true)),
            ("topological_nodes".to_string(), JsonValue::Number(0)),
            ("cycle_nodes".to_string(), JsonValue::Number(0)),
            ("edge_kinds".to_string(), JsonValue::Object(vec![])),
            ("knowledge_statuses".to_string(), JsonValue::Object(vec![])),
        ])
    }

    pub(super) fn is_dag(&self) -> bool {
        self.cycle_nodes().is_empty()
    }

    pub(super) fn topological_order(&self) -> Vec<String> {
        let (order, _) = self.topology();
        order
    }

    pub(super) fn cycle_nodes(&self) -> Vec<String> {
        let (_, cycle_nodes) = self.topology();
        cycle_nodes
    }

    pub(super) fn topology(&self) -> (Vec<String>, Vec<String>) {
        let mut indegree = self
            .nodes
            .iter()
            .map(|node| (node.id.clone(), 0usize))
            .collect::<HashMap<_, _>>();
        let mut outgoing = HashMap::<String, Vec<String>>::new();
        for edge in self.edges.iter() {
            if !indegree.contains_key(&edge.from) || !indegree.contains_key(&edge.to) {
                continue;
            }
            *indegree.entry(edge.to.clone()).or_insert(0) += 1;
            outgoing
                .entry(edge.from.clone())
                .or_default()
                .push(edge.to.clone());
        }
        let mut ready = indegree
            .iter()
            .filter(|(_, degree)| **degree == 0)
            .map(|(node_id, _)| node_id.clone())
            .collect::<Vec<_>>();
        ready.sort();
        let mut order = vec![];
        while !ready.is_empty() {
            let node_id = ready.remove(0);
            order.push(node_id.clone());
            let mut next_nodes = outgoing.get(&node_id).cloned().unwrap_or_default();
            next_nodes.sort();
            for next in next_nodes {
                let Some(degree) = indegree.get_mut(&next) else {
                    continue;
                };
                *degree -= 1;
                if *degree == 0 {
                    ready.push(next);
                    ready.sort();
                }
            }
        }
        let unresolved_nodes = indegree
            .into_iter()
            .filter(|(node_id, degree)| *degree > 0 && !order.contains(node_id))
            .map(|(node_id, _)| node_id)
            .collect::<Vec<_>>();
        let unresolved = unresolved_nodes.iter().cloned().collect::<HashSet<_>>();
        let mut cycle_nodes = unresolved_nodes
            .into_iter()
            .filter(|node_id| node_is_in_cycle(node_id, &outgoing, &unresolved))
            .collect::<Vec<_>>();
        cycle_nodes.sort();
        (order, cycle_nodes)
    }

    pub(super) fn mermaid(&self) -> String {
        let mut output = String::from("flowchart LR\n");
        for node in &self.nodes {
            output.push_str(
                format!("    {}{}\n", mermaid_id(&node.id), mermaid_node_shape(node)).as_str(),
            );
        }
        for edge in &self.edges {
            output.push_str(
                format!(
                    "    {} -->|{}| {}\n",
                    mermaid_id(&edge.from),
                    edge.kind,
                    mermaid_id(&edge.to)
                )
                .as_str(),
            );
        }
        output.trim_end().to_string()
    }
}
