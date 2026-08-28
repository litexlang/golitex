//! Project-reference edges and export-tree authorization.

use super::*;

pub(super) fn config_import_edges(runtime: &Runtime) -> HashMap<ModuleId, Vec<ModuleId>> {
    let mut module_import_edges = HashMap::new();
    let module_ids = runtime
        .module_manager
        .modules
        .keys()
        .copied()
        .collect::<Vec<ModuleId>>();
    for module_id in module_ids {
        let imported_modules = runtime
            .module_manager
            .module(module_id)
            .expect("discovered module should exist")
            .config_imports
            .iter()
            .map(|config_import| config_import.module_id)
            .collect::<Vec<ModuleId>>();
        if imported_modules.is_empty() {
            continue;
        }
        module_import_edges.insert(module_id, imported_modules);
    }
    module_import_edges
}

pub(super) fn reject_unauthorized_project_references(
    runtime: &Runtime,
) -> Result<(), RuntimeError> {
    let files = runtime
        .module_manager
        .modules
        .values()
        .flat_map(|module| {
            module
                .files
                .iter()
                .map(|file| (module.id, file.source_path.clone()))
                .collect::<Vec<(ModuleId, String)>>()
        })
        .collect::<Vec<(ModuleId, String)>>();
    for (owner_module_id, source_path) in files {
        let source = fs::read_to_string(&source_path).map_err(|error| {
            repository_error(
                format!("failed to read module source `{}`: {}", source_path, error),
                &source_path,
                0,
            )
        })?;
        let tokenizer = Tokenizer::new();
        let mut references = vec![];
        // Authorization discovery is lexical: unexecuted later drafts must not
        // need valid block indentation before an earlier prefix can run.
        let source = tokenizer.strip_triple_quote_comment_blocks(&source);
        for (line_index, line) in source.lines().enumerate() {
            let line_file = (line_index + 1, Rc::from(source_path.as_str()));
            let tokens = tokenizer.tokenize_line(line, line_file.clone())?;
            collect_project_reference_targets(
                runtime,
                owner_module_id,
                tokens.as_slice(),
                line_file,
                &mut references,
            );
        }
        for (target, line_file) in references {
            if project_target_is_authorized_for_module(runtime, owner_module_id, target) {
                continue;
            }
            let name = runtime
                .module_manager
                .canonical_name_for_target(target)
                .unwrap_or("project entry");
            return Err(ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                format!(
                    "project dependency `{}` is not authorized for this subpackage; declare its package in an ancestor litex.config [import]",
                    name
                ),
                line_file,
            ))
            .into());
        }
    }
    Ok(())
}

pub(super) fn collect_project_reference_targets(
    runtime: &Runtime,
    owner_module_id: ModuleId,
    tokens: &[String],
    line_file: LineFile,
    references: &mut Vec<(ImportTarget, LineFile)>,
) {
    for start in 0..tokens.len() {
        if start > 0 && tokens[start - 1] == MOD_SIGN {
            continue;
        }
        let mut candidate = tokens[start].clone();
        let mut index = start;
        let mut longest_match = runtime
            .module_manager
            .canonical_name_for_reference(owner_module_id, candidate.as_str())
            .and_then(|name| {
                runtime
                    .module_manager
                    .import_target_by_canonical_name(name.as_str())
            });
        while tokens.get(index + 1).map(String::as_str) == Some(MOD_SIGN) {
            let Some(next) = tokens.get(index + 2) else {
                break;
            };
            candidate = format!("{}{}{}", candidate, MOD_SIGN, next);
            index += 2;
            if let Some(target) = runtime
                .module_manager
                .canonical_name_for_reference(owner_module_id, candidate.as_str())
                .and_then(|name| {
                    runtime
                        .module_manager
                        .import_target_by_canonical_name(name.as_str())
                })
            {
                longest_match = Some(target);
            }
        }
        if let Some(target) = longest_match {
            if !references.iter().any(|(known, _)| *known == target) {
                references.push((target, line_file.clone()));
            }
        }
    }
}

pub(super) fn project_target_is_authorized_for_module(
    runtime: &Runtime,
    owner_module_id: ModuleId,
    target: ImportTarget,
) -> bool {
    let mut package_root_id = owner_module_id;
    while let Some(parent_module_id) = runtime
        .module_manager
        .module(package_root_id)
        .and_then(|module| module.parent_module_id)
    {
        package_root_id = parent_module_id;
    }
    if target_belongs_to_export_tree(runtime, package_root_id, target) {
        return true;
    }
    let mut current_module_id = Some(owner_module_id);
    while let Some(module_id) = current_module_id {
        let Some(module) = runtime.module_manager.module(module_id) else {
            return false;
        };
        for config_import in module.config_imports.iter() {
            if target == ImportTarget::Module(config_import.module_id)
                || target_belongs_to_export_tree(runtime, config_import.module_id, target)
            {
                return true;
            }
        }
        current_module_id = module.parent_module_id;
    }
    false
}

pub(super) fn target_belongs_to_export_tree(
    runtime: &Runtime,
    owner_module_id: ModuleId,
    target: ImportTarget,
) -> bool {
    let Some(module) = runtime.module_manager.module(owner_module_id) else {
        return false;
    };
    module.run_targets.iter().copied().any(|entry| {
        entry == target
            || matches!(entry, ImportTarget::Module(module_id) if target_belongs_to_export_tree(runtime, module_id, target))
    })
}
