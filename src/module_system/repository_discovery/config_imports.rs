//! Configured module imports and registration.

use super::*;

pub(super) fn discover_config_import(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    config_path: &Path,
    import: ProjectImport,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ConfigImport, RuntimeError> {
    let owner_root = {
        let owner = runtime
            .module_manager
            .module(owner_module_id)
            .expect("manifest owner module should exist");
        owner
            .root_directory_path()
            .map(|path| path.as_path().to_path_buf())
            .unwrap_or_default()
    };
    let target_path = owner_root.join(&import.path);
    let canonical_root = canonical_directory(
        &target_path.to_string_lossy(),
        &config_path.to_string_lossy(),
        import.line,
    )?;
    let child_config_path =
        require_project_config(&canonical_root, &config_path.to_string_lossy(), import.line)?;
    let child_root_string =
        path_string(&canonical_root, &config_path.to_string_lossy(), import.line)?;
    let child_config_string = path_string(
        &child_config_path,
        &config_path.to_string_lossy(),
        import.line,
    )?;
    if canonical_root.starts_with(&owner_root) {
        return Err(repository_error(
            "[import] must point to an external module root, not a descendant of the current module"
                .to_string(),
            &config_path.to_string_lossy(),
            import.line,
        ));
    }
    let child_config = read_project_config(&child_config_path)?;
    if child_config.hierarchy != ProjectHierarchy::Module {
        return Err(repository_error(
            "[import] target must declare `module` under [hierarchy]".to_string(),
            &child_config_path.to_string_lossy(),
            child_config.hierarchy_line,
        ));
    }
    reject_module_with_configured_parent(&canonical_root, &child_config_path, &child_config)?;
    let owner_name = runtime
        .module_manager
        .module(owner_module_id)
        .map(|module| module.module_name.clone())
        .unwrap_or_default();
    let child_name = join_module_name(owner_name.as_str(), import.name.as_str());
    reject_active_mount_cycle(
        runtime,
        mount_stack,
        child_root_string.as_str(),
        child_name.as_str(),
        "cyclic config import",
        config_path,
        import.line,
    )?;
    if let Some(existing_module_id) = runtime
        .module_manager
        .module_id_by_root_path(&RealDirectoryPath::new(child_root_string.clone()))
    {
        let duplicate_in_owner =
            runtime
                .module_manager
                .module(owner_module_id)
                .is_some_and(|owner| {
                    owner
                        .config_imports
                        .iter()
                        .any(|existing| existing.module_id == existing_module_id)
                });
        if duplicate_in_owner {
            let existing_name = runtime
                .module_manager
                .module(existing_module_id)
                .map(|module| module.module_name.as_str())
                .unwrap_or("<unknown>");
            return Err(repository_error(
                format!(
                    "physical module is already imported here as `{}`; duplicate alias `{}` is not allowed",
                    existing_name, import.name
                ),
                &config_path.to_string_lossy(),
                import.line,
            ));
        }
        return Ok(ConfigImport {
            name: import.name,
            module_id: existing_module_id,
            kind: ConfigImportKind::Path,
            line_file: (
                import.line,
                Rc::from(config_path.to_string_lossy().to_string()),
            ),
        });
    }
    let child_module_id = runtime
        .module_manager
        .create_discovered_module(
            child_name,
            RealDirectoryPath::new(child_root_string),
            RealFilePath::new(child_config_string),
            ProjectHierarchy::Module,
            None,
        )
        .map_err(|message| {
            repository_error(message, &config_path.to_string_lossy(), import.line)
        })?;
    mount_stack.push(child_module_id);
    let discovery = discover_module_config(
        runtime,
        child_module_id,
        &child_config_path,
        child_config,
        mount_stack,
    );
    mount_stack.pop();
    discovery?;
    Ok(ConfigImport {
        name: import.name,
        module_id: child_module_id,
        kind: ConfigImportKind::Path,
        line_file: (
            import.line,
            Rc::from(config_path.to_string_lossy().to_string()),
        ),
    })
}

pub(super) fn append_config_import(
    runtime: &mut Runtime,
    module_id: ModuleId,
    config_import: ConfigImport,
) {
    let module = runtime
        .module_manager
        .module_mut(module_id)
        .expect("manifest owner module should exist");
    if module
        .config_imports
        .iter()
        .any(|existing| existing.module_id == config_import.module_id)
    {
        return;
    }
    module.config_imports.push(config_import);
}
