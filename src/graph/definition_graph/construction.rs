//! Graph construction and module environment traversal.

use super::*;

impl DefinitionGraphBuilder {
    pub(super) fn new() -> Self {
        Self {
            nodes: vec![],
            node_index: HashMap::new(),
            edges: vec![],
            edge_index: HashMap::new(),
            active_canonical_name: None,
            canonical_name_by_source: HashMap::new(),
        }
    }

    pub(super) fn from_runtime(
        runtime: &Runtime,
        selected_target: Option<RepositoryFileTarget>,
        stmt_results: &[StmtResult],
    ) -> Self {
        let mut builder = Self::new();
        match selected_target {
            Some(RepositoryFileTarget::File { module_id, file_id }) => {
                if let Some(file) = runtime
                    .module_manager
                    .module(module_id)
                    .and_then(|module| module.file(file_id))
                {
                    let node_ids = builder.add_environment(
                        file.environment.as_ref(),
                        Some(file.canonical_name.as_str()),
                        Some(file.source_path.as_str()),
                    );
                    builder.add_execution_source_for_nodes(
                        runtime,
                        file.execution_mode,
                        file.canonical_name.as_str(),
                        file.source_path.as_str(),
                        node_ids.as_slice(),
                    );
                }
            }
            Some(RepositoryFileTarget::Module(module_id)) => {
                builder.add_module_environments(runtime, module_id);
            }
            None => {
                if let Some(module_id) = runtime.module_manager.entry_module_id {
                    builder.add_module_environments(runtime, module_id);
                }
            }
        }
        builder.add_result_provenance(stmt_results);
        builder.propagate_knowledge_status();
        builder
    }

    pub(super) fn add_module_environments(
        &mut self,
        runtime: &Runtime,
        target_module_id: ModuleId,
    ) {
        let mut module_ids = runtime
            .module_manager
            .modules
            .keys()
            .copied()
            .filter(|module_id| {
                definition_graph_module_is_descendant(runtime, *module_id, target_module_id)
            })
            .collect::<Vec<_>>();
        module_ids.sort_by_key(|module_id| module_id.0);
        for module_id in module_ids {
            let Some(module) = runtime.module_manager.module(module_id) else {
                continue;
            };
            let main_node_ids = self.add_environment(
                module.main_environment.as_ref(),
                Some(module.module_name.as_str()),
                Some(module.main_file_path.as_str()),
            );
            self.add_execution_source_for_nodes(
                runtime,
                module.execution_mode,
                module.module_name.as_str(),
                module.main_file_path.as_str(),
                main_node_ids.as_slice(),
            );
            for file in module.files.iter() {
                if file.status != FileStatus::Loaded {
                    continue;
                }
                let node_ids = self.add_environment(
                    file.environment.as_ref(),
                    Some(file.canonical_name.as_str()),
                    Some(file.source_path.as_str()),
                );
                self.add_execution_source_for_nodes(
                    runtime,
                    file.execution_mode,
                    file.canonical_name.as_str(),
                    file.source_path.as_str(),
                    node_ids.as_slice(),
                );
            }
        }
    }

    pub(super) fn add_environment(
        &mut self,
        environment: &Environment,
        canonical_name: Option<&str>,
        source_path: Option<&str>,
    ) -> Vec<String> {
        let previous_canonical_name = self.active_canonical_name.clone();
        self.active_canonical_name = canonical_name
            .filter(|name| !name.is_empty())
            .map(str::to_string);
        if let (Some(canonical_name), Some(source_path)) =
            (self.active_canonical_name.as_ref(), source_path)
        {
            self.canonical_name_by_source
                .insert(source_path.to_string(), canonical_name.clone());
        }
        let defined_before = self
            .nodes
            .iter()
            .filter(|node| node.defined)
            .map(|node| node.id.clone())
            .collect::<HashSet<_>>();
        self.add_identifiers(environment);
        self.add_props(environment);
        self.add_functions(environment);
        self.add_algorithms(environment);
        self.add_structs(environment);
        self.add_templates(environment);
        self.add_theorems(environment);
        self.add_strategies(environment);
        let node_ids = self
            .nodes
            .iter()
            .filter(|node| node.defined && !defined_before.contains(&node.id))
            .map(|node| node.id.clone())
            .collect();
        self.active_canonical_name = previous_canonical_name;
        node_ids
    }
}
