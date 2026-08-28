//! Terminal module imports and target paths.

use super::*;

pub fn discover_terminal_module_import(
    runtime: &mut Runtime,
    import_path: &str,
    alias: &str,
    line_file: LineFile,
) -> Result<ModuleId, RuntimeError> {
    let importing_module_id = runtime.current_module_id();
    let source_path = line_file.1.as_ref();
    let target_path = terminal_import_target_path(runtime, import_path, source_path)?;
    let canonical_root = canonical_directory(
        target_path.to_string_lossy().as_ref(),
        source_path,
        line_file.0,
    )?;
    let config_path = require_project_config(&canonical_root, source_path, line_file.0)?;
    let config = read_project_config(&config_path)?;
    if config.hierarchy != ProjectHierarchy::Module {
        return Err(repository_error(
            "terminal import target must declare module under [hierarchy]".to_string(),
            &config_path.to_string_lossy(),
            config.hierarchy_line,
        ));
    }
    reject_module_with_configured_parent(&canonical_root, &config_path, &config)?;

    let root_string = path_string(&canonical_root, source_path, line_file.0)?;
    let config_string = path_string(&config_path, source_path, line_file.0)?;
    let mut mount_stack = vec![importing_module_id];
    reject_active_mount_cycle(
        runtime,
        mount_stack.as_slice(),
        root_string.as_str(),
        alias,
        "cyclic terminal import",
        &config_path,
        line_file.0,
    )?;
    if let Some(existing_module_id) = runtime.module_manager.module_id_by_path(&root_string) {
        let existing_name = runtime
            .module_manager
            .module(existing_module_id)
            .map(|module| module.module_name.as_str())
            .unwrap_or("<unknown>");
        return Err(repository_error(
            format!(
                "physical module is already registered as `{}`; it cannot also be imported as `{}`",
                existing_name, alias
            ),
            source_path,
            line_file.0,
        ));
    }
    let module_id = runtime
        .module_manager
        .create_discovered_module(
            alias.to_string(),
            root_string,
            config_string,
            ProjectHierarchy::Module,
            None,
        )
        .map_err(|message| repository_error(message, source_path, line_file.0))?;
    mount_stack.push(module_id);
    let discovery =
        discover_module_config(runtime, module_id, &config_path, config, &mut mount_stack);
    mount_stack.pop();
    discovery?;
    reject_unauthorized_project_references(runtime)?;
    let import_edges = config_import_edges(runtime);
    reject_cyclic_module_imports(runtime, &import_edges)?;
    Ok(module_id)
}

pub(super) fn terminal_import_target_path(
    runtime: &Runtime,
    import_path: &str,
    source_path: &str,
) -> Result<PathBuf, RuntimeError> {
    let target = PathBuf::from(import_path);
    if target.is_absolute() {
        return Ok(target);
    }
    let current_file_path = runtime.current_file_path_rc();
    let current_path = Path::new(current_file_path.as_ref());
    if current_path.is_absolute() {
        if let Some(parent) = current_path.parent() {
            return Ok(parent.join(target));
        }
    }
    let current_dir = env::current_dir().map_err(|error| {
        repository_error(
            format!("could not inspect the current directory: {}", error),
            source_path,
            0,
        )
    })?;
    Ok(current_dir.join(target))
}
