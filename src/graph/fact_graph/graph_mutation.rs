//! Node identity, insertion, and edge mutation.

use super::*;

impl FactGraphBuilder {
    pub(super) fn last_factual_success_node_id(
        &mut self,
        success: &SuccessStmtResult,
    ) -> Option<String> {
        if let Some(fact) = success.fact() {
            return Some(self.add_fact_node(&fact.fact(), "fact", None));
        }
        if let Stmt::By(ByStmt::ByDefStmt(stmt)) = &success.statement() {
            let fact: Fact = stmt.fact.clone().into();
            return Some(self.add_fact_node(&fact, "fact", None));
        }
        let mut last_child_id = None;
        success.visit_child_results(&mut |child| {
            if let Some(node_id) = self.last_factual_result_node_id(std::slice::from_ref(child)) {
                last_child_id = Some(node_id);
            }
        });
        success.visit_success_child_results(&mut |child| {
            if let Some(node_id) = self.last_factual_success_node_id(child) {
                last_child_id = Some(node_id);
            }
        });
        last_child_id
    }

    pub(super) fn add_fact_node(
        &mut self,
        fact: &Fact,
        fact_kind: &str,
        reason: Option<&String>,
    ) -> String {
        let node_id = fact_node_id(fact);
        let label = format!(
            "{} · {}",
            line_label(&fact.line_file()),
            compact_text(&fact.to_string())
        );
        self.ensure_node(
            node_id.clone(),
            "fact",
            label,
            Some(&fact.line_file()),
            Some(&fact.to_string()),
            Some(fact_kind),
            reason,
        );
        node_id
    }

    pub(super) fn ensure_node(
        &mut self,
        id: String,
        kind: &str,
        label: String,
        line_file: Option<&LineFile>,
        statement: Option<&String>,
        fact_kind: Option<&str>,
        reason: Option<&String>,
    ) {
        if let Some(index) = self.node_index.get(&id).copied() {
            let node = &mut self.nodes[index];
            if node.statement.is_none() {
                node.statement = statement.cloned();
            }
            if node.line_file.is_none() {
                node.line_file = line_file.cloned();
            }
            if node.reason.is_none() {
                node.reason = reason.cloned();
            }
            if let Some(fact_kind) = fact_kind {
                if node.fact_kind.as_deref() == Some("reference") || node.fact_kind.is_none() {
                    node.fact_kind = Some(fact_kind.to_string());
                }
            }
            return;
        }
        self.node_index.insert(id.clone(), self.nodes.len());
        self.nodes.push(FactGraphNode {
            id,
            kind: kind.to_string(),
            label,
            fact_kind: fact_kind.map(|kind| kind.to_string()),
            line_file: line_file.cloned(),
            statement: statement.cloned(),
            reason: reason.cloned(),
        });
    }

    pub(super) fn add_edge(&mut self, from: &str, to: &str, kind: &str) {
        if from == to {
            return;
        }
        let key = format!("{}|{}|{}", from, to, kind);
        if let Some(index) = self.edge_index.get(&key).copied() {
            self.edges[index].count += 1;
            return;
        }
        self.edge_index.insert(key, self.edges.len());
        self.edges.push(FactGraphEdge {
            from: from.to_string(),
            to: to.to_string(),
            kind: kind.to_string(),
            count: 1,
        });
    }
}
