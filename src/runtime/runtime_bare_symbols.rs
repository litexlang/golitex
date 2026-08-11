use crate::prelude::*;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug)]
pub struct BareSymbol {
    pub canonical_owner: String,
    pub symbol: SymbolRef,
    pub role: SymbolRole,
    pub source_name: String,
    pub source_kind: BareSymbolSourceKind,
    pub source_line_file: LineFile,
}

#[derive(Clone)]
struct BareSymbolCandidate {
    local_name: String,
    canonical_owner: String,
    symbol: SymbolRef,
    role: SymbolRole,
}

impl Runtime {
    /// Rebuild the current source's bare-name index once, after configured
    /// imports and any preceding export targets have finished loading.
    pub(crate) fn refresh_current_bare_symbol_index(&mut self) -> Result<(), RuntimeError> {
        let module_id = self.current_module_id();
        let sources = self.inherited_bare_symbol_sources(module_id);
        let mut index: HashMap<String, BareSymbol> = HashMap::new();
        let mut seen_symbols = HashSet::new();

        for source in sources {
            if !self.bare_symbol_source_is_loaded(source.target) {
                continue;
            }
            let mut candidates = Vec::new();
            let mut visited_targets = HashSet::new();
            self.collect_public_bare_symbol_candidates(
                source.target,
                &mut visited_targets,
                &mut candidates,
            );
            candidates.sort_by(|left, right| {
                left.local_name
                    .cmp(&right.local_name)
                    .then_with(|| left.canonical_owner.cmp(&right.canonical_owner))
                    .then_with(|| left.symbol.id().value().cmp(&right.symbol.id().value()))
            });

            for candidate in candidates {
                if !seen_symbols.insert(candidate.symbol.id()) {
                    continue;
                }
                let entry = BareSymbol {
                    canonical_owner: candidate.canonical_owner,
                    symbol: candidate.symbol,
                    role: candidate.role,
                    source_name: source.name.clone(),
                    source_kind: source.kind,
                    source_line_file: source.line_file.clone(),
                };
                if let Some(existing) = index.get(&candidate.local_name) {
                    return Err(bare_symbol_conflict_error(
                        &candidate.local_name,
                        existing,
                        &entry,
                    ));
                }
                index.insert(candidate.local_name, entry);
            }
        }

        self.execution_stack
            .last_mut()
            .expect("an execution frame should exist while refreshing bare symbols")
            .bare_symbols = index;
        Ok(())
    }

    pub(crate) fn bare_symbol(&self, name: &str) -> Option<&BareSymbol> {
        self.execution_stack.last()?.bare_symbols.get(name)
    }

    fn inherited_bare_symbol_sources(&self, module_id: ModuleId) -> Vec<ConfigBareSymbolSource> {
        let mut sources = Vec::new();
        let mut current = Some(module_id);
        while let Some(current_id) = current {
            let Some(module) = self.module_manager.module(current_id) else {
                break;
            };
            sources.extend(module.bare_symbol_sources.iter().cloned());
            current = module.parent_module_id;
        }
        sources
    }

    fn bare_symbol_source_is_loaded(&self, target: ImportTarget) -> bool {
        match target {
            ImportTarget::Module(module_id) => self
                .module_manager
                .module(module_id)
                .is_some_and(|module| module.status == ModuleStatus::Loaded),
            ImportTarget::File { module_id, file_id } => self
                .module_manager
                .module(module_id)
                .and_then(|module| module.file(file_id))
                .is_some_and(|file| file.status == FileStatus::Loaded),
        }
    }

    fn collect_public_bare_symbol_candidates(
        &self,
        target: ImportTarget,
        visited_targets: &mut HashSet<ImportTarget>,
        output: &mut Vec<BareSymbolCandidate>,
    ) {
        if !visited_targets.insert(target) {
            return;
        }
        match target {
            ImportTarget::File { module_id, file_id } => {
                let Some(module) = self.module_manager.module(module_id) else {
                    return;
                };
                let Some(file) = module.file(file_id) else {
                    return;
                };
                if file.status != FileStatus::Loaded {
                    return;
                }
                collect_environment_symbols(
                    file.environment.as_ref(),
                    file.canonical_name.as_str(),
                    output,
                );
            }
            ImportTarget::Module(module_id) => {
                let Some(module) = self.module_manager.module(module_id) else {
                    return;
                };
                if module.status != ModuleStatus::Loaded {
                    return;
                }
                if module.main_file_path.ends_with(".lit") {
                    collect_environment_symbols(
                        module.main_environment.as_ref(),
                        module.module_name.as_str(),
                        output,
                    );
                    return;
                }
                for child in module.run_targets.iter().copied() {
                    self.collect_public_bare_symbol_candidates(child, visited_targets, output);
                }
            }
        }
    }
}

fn collect_environment_symbols(
    environment: &Environment,
    canonical_owner: &str,
    output: &mut Vec<BareSymbolCandidate>,
) {
    for (local_name, definition) in environment.symbols.iter() {
        if !definition.role().is_public_declaration() {
            continue;
        }
        output.push(BareSymbolCandidate {
            local_name: local_name.clone(),
            canonical_owner: canonical_owner.to_string(),
            symbol: definition.binding().as_ref(),
            role: definition.role(),
        });
    }
}

fn bare_symbol_conflict_error(
    local_name: &str,
    existing: &BareSymbol,
    conflicting: &BareSymbol,
) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        format!(
            "{} `{}` exposes ambiguous bare symbol `{}`: `{}` ({}) and `{}` ({}) are different symbols",
            conflicting.source_kind.table_name(),
            conflicting.source_name,
            local_name,
            existing.canonical_owner,
            existing.role.description(),
            conflicting.canonical_owner,
            conflicting.role.description(),
        ),
        conflicting.source_line_file.clone(),
    ))
    .into()
}
