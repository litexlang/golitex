//! Module configuration and active mount cycles.

use super::*;

pub(super) fn discover_module_config(
    runtime: &mut Runtime,
    module_id: ModuleId,
    config_path: &Path,
    config: ProjectConfig,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<(), RuntimeError> {
    let module_flatten = config.module_flatten;
    let module_flatten_line = config.module_flatten_line;
    let module_hierarchy = runtime
        .module_manager
        .module(module_id)
        .map(|module| module.hierarchy)
        .ok_or_else(|| {
            repository_error(
                "manifest owner module is missing".to_string(),
                &config_path.to_string_lossy(),
                0,
            )
        })?;
    if module_hierarchy != config.hierarchy {
        return Err(repository_error(
            "litex.config hierarchy does not match how this folder is mounted".to_string(),
            &config_path.to_string_lossy(),
            config.hierarchy_line,
        ));
    }
    validate_config_export_paths(config_path, &config)?;
    for import in config.imports.iter().cloned() {
        let config_import =
            discover_config_import(runtime, module_id, config_path, import, mount_stack)?;
        append_config_import(runtime, module_id, config_import);
    }
    for import in config.std_imports.iter().cloned() {
        let config_import =
            discover_config_std_import(runtime, module_id, config_path, import, mount_stack)?;
        append_config_import(runtime, module_id, config_import);
    }

    for export in config.exports {
        let already_discovered = runtime
            .module_manager
            .module(module_id)
            .expect("manifest owner module should exist")
            .exports
            .contains_key(&export.name);
        if already_discovered {
            continue;
        }
        let line_file = (
            export.line,
            Rc::from(config_path.to_string_lossy().to_string()),
        );
        let target = discover_config_export(runtime, module_id, config_path, export, mount_stack)?;
        let module = runtime
            .module_manager
            .module_mut(module_id)
            .expect("manifest owner module should exist");
        module.run_targets.push(target);
        module.run_target_lines.insert(target, line_file);
    }
    if module_flatten {
        let module = runtime
            .module_manager
            .module_mut(module_id)
            .expect("manifest owner module should exist");
        let Some(ImportTarget::File { source_id, .. }) = module.run_targets.first().copied() else {
            return Err(repository_error(
                "[module] flatten requires exactly one exported file".to_string(),
                &config_path.to_string_lossy(),
                module_flatten_line.unwrap_or(config.hierarchy_line),
            ));
        };
        module.flattened_export_source = Some(source_id);
    }
    Ok(())
}

pub(super) fn reject_active_mount_cycle(
    runtime: &Runtime,
    mount_stack: &[ModuleId],
    child_root_path: &str,
    child_name: &str,
    kind: &str,
    config_path: &Path,
    line: usize,
) -> Result<(), RuntimeError> {
    let Some(start) = mount_stack.iter().position(|module_id| {
        runtime
            .module_manager
            .module(*module_id)
            .is_some_and(|module| {
                module
                    .root_directory_path()
                    .is_some_and(|path| path.to_string() == child_root_path)
            })
    }) else {
        return Ok(());
    };
    let mut names = mount_stack[start..]
        .iter()
        .filter_map(|module_id| runtime.module_manager.module(*module_id))
        .map(|module| {
            if module.module_name.is_empty() {
                "<root>".to_string()
            } else {
                module.module_name.clone()
            }
        })
        .collect::<Vec<String>>();
    names.push(child_name.to_string());
    Err(repository_error(
        format!("{}: {}", kind, names.join(" -> ")),
        &config_path.to_string_lossy(),
        line,
    ))
}
