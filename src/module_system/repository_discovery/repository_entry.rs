//! Repository discovery entrypoints and requested targets.

use super::*;

pub fn discover_repository(
    runtime: &mut Runtime,
    repository_path: &str,
) -> Result<RepositoryFileTarget, RuntimeError> {
    let requested_root = canonical_directory(repository_path, repository_path, 0)?;
    let requested_config_path = require_project_config(&requested_root, repository_path, 0)?;
    let requested_config = read_project_config(&requested_config_path)?;
    let repository_root = enclosing_module_root(
        &requested_root,
        &requested_config_path,
        &requested_config,
        repository_path,
    )?;
    let config_path = require_project_config(&repository_root, repository_path, 0)?;
    let config = read_project_config(&config_path)?;
    if config.hierarchy != ProjectHierarchy::Module {
        return Err(repository_error(
            "the top-level litex.config must declare `module` under [hierarchy]".to_string(),
            &config_path.to_string_lossy(),
            config.hierarchy_line,
        ));
    }
    let repository_root_string = path_string(&repository_root, repository_path, 0)?;
    let config_path_string = path_string(&config_path, repository_path, 0)?;
    let root_module_id = runtime
        .start_repository_run(repository_root_string, config_path_string.clone())
        .map_err(|message| repository_error(message, repository_path, 0))?;

    let mut mount_stack = vec![root_module_id];
    discover_module_config(
        runtime,
        root_module_id,
        &config_path,
        config,
        &mut mount_stack,
    )?;
    reject_unauthorized_project_references(runtime)?;
    let module_import_edges = config_import_edges(runtime);
    reject_cyclic_module_imports(runtime, &module_import_edges)?;
    if requested_root == repository_root {
        return Ok(RepositoryFileTarget::Module(root_module_id));
    }
    let requested_root_string = path_string(&requested_root, repository_path, 0)?;
    let target_module_id = runtime
        .module_manager
        .modules
        .values()
        .find(|module| {
            module.module_root_path == requested_root_string
                && runtime
                    .module_manager
                    .module_is_descendant_of(module.id, root_module_id)
        })
        .map(|module| module.id)
        .ok_or_else(|| {
            repository_error(
                format!(
                    "submodule directory `{}` is not exported by its parent hierarchy",
                    requested_root_string
                ),
                repository_path,
                0,
            )
        })?;
    Ok(RepositoryFileTarget::Module(target_module_id))
}

pub fn discover_repository_for_file(
    runtime: &mut Runtime,
    file_path: &str,
) -> Result<Option<RepositoryFileTarget>, RuntimeError> {
    let canonical_file = fs::canonicalize(file_path).map_err(|error| {
        repository_error(
            format!("source file `{}` does not exist: {}", file_path, error),
            file_path,
            0,
        )
    })?;
    if !canonical_file.is_file() {
        return Err(repository_error(
            format!("source path `{}` is not a file", file_path),
            file_path,
            0,
        ));
    }
    let Some(parent) = canonical_file.parent() else {
        return Ok(None);
    };
    if !parent.join(LITEX_CONFIG).is_file() {
        return Ok(None);
    }
    let parent_string = path_string(parent, file_path, 0)?;
    discover_repository(runtime, parent_string.as_str())?;
    let canonical_file_string = path_string(&canonical_file, file_path, 0)?;
    let targets = repository_targets_for_path(runtime, canonical_file_string.as_str());
    if targets.len() != 1 {
        return Err(repository_error(
            format!(
                "source file `{}` must be exported exactly once by its containing litex.config",
                canonical_file_string
            ),
            file_path,
            0,
        ));
    }
    Ok(targets.into_iter().next())
}

pub(super) fn repository_targets_for_path(
    runtime: &Runtime,
    source_path: &str,
) -> Vec<RepositoryFileTarget> {
    let mut targets = vec![];
    for module in runtime.module_manager.modules.values() {
        for file in module.files.iter() {
            if file.source_path == source_path {
                targets.push(RepositoryFileTarget::File {
                    module_id: module.id,
                    file_id: file.id,
                });
            }
        }
    }
    targets
}
