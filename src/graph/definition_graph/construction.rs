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
            Some(RepositoryFileTarget::File {
                module_id,
                source_id,
            }) => {
                if let Some(source) = runtime
                    .module_manager
                    .module(module_id)
                    .and_then(|module| module.source(source_id))
                {
                    let source_label = source.display_label();
                    let node_ids = builder.add_environment(
                        source.environment.as_ref(),
                        source.canonical_name.as_deref(),
                        Some(source_label.as_str()),
                    );
                    builder.add_execution_source_for_nodes(
                        runtime,
                        source.load_mode,
                        source.canonical_name.as_deref().unwrap_or_default(),
                        source_label.as_str(),
                        node_ids.as_slice(),
                    );
                }
            }
            Some(RepositoryFileTarget::Module(module_id)) => {
                builder.add_module_environments(runtime, module_id);
            }
            None => {
                if runtime.module_manager.module(ModuleId::ROOT).is_some() {
                    builder.add_module_environments(runtime, ModuleId::ROOT);
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
            let main_source_label = module.main_source_label();
            let main_node_ids = self.add_environment(
                module.main_environment.as_ref(),
                Some(module.module_name.as_str()),
                Some(main_source_label.as_str()),
            );
            self.add_execution_source_for_nodes(
                runtime,
                module.load_mode,
                module.module_name.as_str(),
                main_source_label.as_str(),
                main_node_ids.as_slice(),
            );
            for source in module.sources.iter() {
                if source.load_status != SourceLoadStatus::Loaded {
                    continue;
                }
                // Repository/file graph projection includes physical sources;
                // a standalone or session graph may additionally include only
                // the one virtual source that is currently active. Historical
                // REPL/session sources must not leak into later projections.
                let is_current_source = runtime.current_module_id == Some(module.id)
                    && runtime.current_source_id == Some(source.id);
                if source.real_file_path().is_none() && !is_current_source {
                    continue;
                }
                let source_label = source.display_label();
                let node_ids = self.add_environment(
                    source.environment.as_ref(),
                    source.canonical_name.as_deref(),
                    Some(source_label.as_str()),
                );
                self.add_execution_source_for_nodes(
                    runtime,
                    source.load_mode,
                    source.canonical_name.as_deref().unwrap_or_default(),
                    source_label.as_str(),
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
