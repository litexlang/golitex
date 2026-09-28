//! Node definition state, source, semantic role, knowledge status, identity, and edges.

use super::*;

impl DefinitionGraphBuilder {
    pub(super) fn node_is_defined(&self, node_id: &str) -> bool {
        self.node_index
            .get(node_id)
            .is_some_and(|index| self.nodes[*index].defined)
    }

    pub(super) fn set_node_litex_form(&mut self, node_id: &str, litex_form: &str) {
        let Some(index) = self.node_index.get(node_id).copied() else {
            return;
        };
        self.nodes[index].litex_form = litex_form.to_string();
    }

    pub(super) fn set_node_source_if_default(
        &mut self,
        node_id: &str,
        line_file: &LineFile,
        statement: &str,
    ) {
        let Some(index) = self.node_index.get(node_id).copied() else {
            return;
        };
        let node = &mut self.nodes[index];
        if node
            .line_file
            .as_ref()
            .map(|existing| existing.0 == 0)
            .unwrap_or(true)
        {
            node.line_file = Some(line_file.clone());
            node.statement = Some(statement.to_string());
        }
    }

    pub(super) fn set_node_semantic_role(&mut self, node_id: &str, semantic_role: &str) {
        let Some(index) = self.node_index.get(node_id).copied() else {
            return;
        };
        self.nodes[index].semantic_role = semantic_role.to_string();
    }

    pub(super) fn set_node_knowledge_status(
        &mut self,
        node_id: &str,
        knowledge_status: &str,
        trust_kind: Option<&str>,
    ) -> bool {
        let Some(index) = self.node_index.get(node_id).copied() else {
            return false;
        };
        let node = &mut self.nodes[index];
        if node.knowledge_status == "axiom" {
            return false;
        }
        if knowledge_status == "axiom" {
            let changed = node.knowledge_status != "axiom";
            node.knowledge_status = "axiom".to_string();
            node.trust_kind = Some("direct".to_string());
            return changed;
        }
        if knowledge_status != "trust" {
            return false;
        }
        let was_status = node.knowledge_status.clone();
        let was_kind = node.trust_kind.clone();
        node.knowledge_status = "trust".to_string();
        if trust_kind == Some("direct") || node.trust_kind.is_none() {
            node.trust_kind = trust_kind.map(str::to_string);
        }
        node.knowledge_status != was_status || node.trust_kind != was_kind
    }

    pub(super) fn propagate_knowledge_status(&mut self) {
        loop {
            let mut changed = false;
            let mut inherited_edges = vec![];
            for edge in self.edges.clone() {
                let Some(source_index) = self.node_index.get(&edge.from).copied() else {
                    continue;
                };
                let source_status = self.nodes[source_index].knowledge_status.as_str();
                if source_status != "axiom" && source_status != "trust" {
                    continue;
                }
                if self.set_node_knowledge_status(&edge.to, "trust", Some("indirect")) {
                    changed = true;
                }
                if edge.kind != "trust_source" {
                    inherited_edges.push((edge.from.clone(), edge.to.clone()));
                }
            }
            for (from, to) in inherited_edges {
                self.add_edge(&from, &to, "trust_source");
            }
            if !changed {
                break;
            }
        }
    }

    pub(super) fn ensure_node(
        &mut self,
        id: String,
        kind: &str,
        definition_kind: &str,
        name: &str,
        defined: bool,
        line_file: Option<&LineFile>,
        statement: Option<&str>,
    ) {
        if let Some(index) = self.node_index.get(&id).copied() {
            let node = &mut self.nodes[index];
            if defined {
                node.defined = true;
                node.definition_kind = definition_kind.to_string();
                node.semantic_role = definition_semantic_role(kind, definition_kind).to_string();
                node.litex_form = definition_litex_form(kind, definition_kind).to_string();
                let (knowledge_status, trust_kind) =
                    default_definition_knowledge_status(definition_kind);
                node.knowledge_status = knowledge_status.to_string();
                node.trust_kind = trust_kind.map(str::to_string);
                node.line_file = line_file.cloned();
                node.statement = statement.map(str::to_string);
            }
            return;
        }
        self.node_index.insert(id.clone(), self.nodes.len());
        let (knowledge_status, trust_kind) = default_definition_knowledge_status(definition_kind);
        self.nodes.push(DefinitionGraphNode {
            id,
            kind: kind.to_string(),
            definition_kind: definition_kind.to_string(),
            name: name.to_string(),
            label: name.to_string(),
            defined,
            semantic_role: definition_semantic_role(kind, definition_kind).to_string(),
            litex_form: definition_litex_form(kind, definition_kind).to_string(),
            knowledge_status: knowledge_status.to_string(),
            trust_kind: trust_kind.map(str::to_string),
            line_file: line_file.cloned(),
            statement: statement.map(str::to_string),
        });
    }

    pub(super) fn add_edge(&mut self, from: &str, to: &str, kind: &str) {
        if from == to {
            return;
        }
        let reference_kind = self
            .node_index
            .get(from)
            .map(|index| self.nodes[*index].kind.clone())
            .unwrap_or_else(|| "unknown".to_string());
        let key = format!("{}|{}|{}|{}", from, to, kind, reference_kind);
        if let Some(index) = self.edge_index.get(&key).copied() {
            self.edges[index].count += 1;
            return;
        }
        self.edge_index.insert(key, self.edges.len());
        self.edges.push(DefinitionGraphEdge {
            from: from.to_string(),
            to: to.to_string(),
            kind: kind.to_string(),
            reference_kind,
            count: 1,
        });
    }
}
