//! Definition dependencies and execution sources.

use super::*;

impl DefinitionGraphBuilder {
    pub(super) fn add_dependency_edges(
        &mut self,
        target_id: &str,
        collector: DepCollector,
        dependency_kind: &str,
    ) {
        for name in collector.deps.props {
            let name = self.normalized_dependency_name(name.as_str());
            let source_id = definition_id("prop", &name);
            self.ensure_node(source_id.clone(), "prop", "prop", &name, false, None, None);
            self.add_edge(&source_id, target_id, dependency_kind);
        }
        for name in collector.deps.fns {
            let name = self.normalized_dependency_name(name.as_str());
            let source_id = definition_id("fn", &name);
            self.ensure_node(
                source_id.clone(),
                "fn",
                "function",
                &name,
                false,
                None,
                None,
            );
            self.add_edge(&source_id, target_id, dependency_kind);
        }
        for name in collector.deps.structs {
            let name = self.normalized_dependency_name(name.as_str());
            let source_id = definition_id("struct", &name);
            self.ensure_node(
                source_id.clone(),
                "struct",
                "structure",
                &name,
                false,
                None,
                None,
            );
            self.add_edge(&source_id, target_id, dependency_kind);
        }
        for name in collector.deps.templates {
            let name = self.normalized_dependency_name(name.as_str());
            let source_id = definition_id("template", &name);
            self.ensure_node(
                source_id.clone(),
                "template",
                "template",
                &name,
                false,
                None,
                None,
            );
            self.add_edge(&source_id, target_id, dependency_kind);
        }
    }

    pub(super) fn normalized_dependency_name(&self, name: &str) -> String {
        let Some(canonical_name) = self.active_canonical_name.as_ref() else {
            return name.to_string();
        };
        let local_prefix = format!("{}{}", canonical_name, MOD_SIGN);
        name.strip_prefix(local_prefix.as_str())
            .map(str::to_string)
            .unwrap_or_else(|| name.to_string())
    }

    pub(super) fn add_execution_source_for_nodes(
        &mut self,
        runtime: &Runtime,
        execution_mode: ExecutionMode,
        canonical_name: &str,
        source_path: &str,
        node_ids: &[String],
    ) {
        if execution_mode == ExecutionMode::Verified || node_ids.is_empty() {
            return;
        }
        let unverified = runtime
            .unverified_imports()
            .iter()
            .find(|entry| entry.name == canonical_name);
        let source_kind = unverified
            .map(|entry| entry.kind.as_str())
            .unwrap_or("trusted_execution");
        let line_file = unverified
            .map(|entry| entry.line_file.clone())
            .unwrap_or_else(|| (0, Rc::from(source_path)));
        let source_name = if canonical_name.is_empty() {
            source_path
        } else {
            canonical_name
        };
        let source_id = trust_source_id(source_kind, Some(source_name), &line_file);
        self.ensure_node(
            source_id.clone(),
            "source",
            "unverified_import",
            source_name,
            true,
            Some(&line_file),
            Some(&format!("{} {}", source_kind, source_name)),
        );
        for node_id in node_ids {
            self.set_node_knowledge_status(node_id, "trust", Some("direct"));
            self.add_edge(&source_id, node_id, "trust_source");
        }
    }
}
