use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::rc::Rc;

const LITEX_CONFIG: &str = "litex.config";
const LITEX_TODO: &str = "todo.lit";
const LOCAL_DRAFTS: &str = ".drafts";

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum RepositoryFileTarget {
    Module(ModuleId),
    File {
        module_id: ModuleId,
        file_id: FileId,
    },
}

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

pub fn discover_terminal_std_import(
    runtime: &mut Runtime,
    package_name: &str,
    line_file: LineFile,
) -> Result<ModuleId, RuntimeError> {
    let importing_module_id = runtime.current_module_id();
    let source_path = line_file.1.as_ref();
    let std_root = resolve_std_root()
        .map_err(|message| repository_error(message, source_path, line_file.0))?;
    let mut mount_stack = vec![importing_module_id];
    let module_id = discover_std_module_with_mount_stack(
        runtime,
        importing_module_id,
        &std_root,
        package_name,
        &mut mount_stack,
    )?;
    reject_unauthorized_project_references(runtime)?;
    let import_edges = config_import_edges(runtime);
    reject_cyclic_module_imports(runtime, &import_edges)?;
    Ok(module_id)
}

pub fn resolve_std_root() -> Result<PathBuf, String> {
    let configured_root = env::var("LITEX_STD_PATH").ok().map(PathBuf::from);
    let current_dir = env::current_dir().ok();
    let executable = env::current_exe().ok();
    for root in standard_library_root_candidates(configured_root, current_dir, executable) {
        if root.is_dir() {
            return Ok(root);
        }
    }
    Err("standard library was not found; searched LITEX_STD_PATH, ./std, and the executable installation paths".to_string())
}

fn discover_std_module_with_mount_stack(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    std_root: &Path,
    package_name: &str,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ModuleId, RuntimeError> {
    let canonical_std_root =
        canonical_directory(&std_root.to_string_lossy(), &std_root.to_string_lossy(), 0)?;
    let single_file_path = canonical_std_root.join(format!("{}.lit", package_name));
    if single_file_path.is_file() {
        return discover_std_single_file_module(
            runtime,
            owner_module_id,
            &canonical_std_root,
            &single_file_path,
            package_name,
            mount_stack,
        );
    }
    let package_root = canonical_std_root.join(package_name);
    let canonical_package_root = canonical_directory(
        &package_root.to_string_lossy(),
        &canonical_std_root.to_string_lossy(),
        0,
    )?;
    let config_path = require_project_config(
        &canonical_package_root,
        &canonical_std_root.to_string_lossy(),
        0,
    )?;
    let config = read_project_config(&config_path)?;
    if config.hierarchy != ProjectHierarchy::Module {
        return Err(repository_error(
            format!(
                "standard package `{}` must declare `module` under [hierarchy]",
                package_name
            ),
            &config_path.to_string_lossy(),
            config.hierarchy_line,
        ));
    }
    let package_root_string =
        path_string(&canonical_package_root, &config_path.to_string_lossy(), 0)?;
    let config_path_string = path_string(&config_path, &config_path.to_string_lossy(), 0)?;
    let owner_name = runtime
        .module_manager
        .module(owner_module_id)
        .map(|module| module.module_name.clone())
        .unwrap_or_default();
    let local_name = package_name.to_string();
    let module_name = join_module_name(owner_name.as_str(), local_name.as_str());
    reject_active_mount_cycle(
        runtime,
        mount_stack,
        package_root_string.as_str(),
        module_name.as_str(),
        "cyclic standard package import",
        &config_path,
        0,
    )?;
    if let Some(existing_module_id) = runtime
        .module_manager
        .module_id_by_path(package_root_string.as_str())
    {
        return Ok(existing_module_id);
    }
    let std_module_id = runtime
        .module_manager
        .create_discovered_standard_module(
            module_name,
            package_root_string,
            config_path_string,
            ProjectHierarchy::Module,
            None,
        )
        .map_err(|message| repository_error(message, &config_path.to_string_lossy(), 0))?;
    mount_stack.push(std_module_id);
    let discovery =
        discover_module_config(runtime, std_module_id, &config_path, config, mount_stack);
    mount_stack.pop();
    discovery?;
    Ok(std_module_id)
}

fn discover_std_single_file_module(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    std_root: &Path,
    source_path: &Path,
    package_name: &str,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ModuleId, RuntimeError> {
    let canonical_source_path = canonical_file(source_path, &std_root.to_string_lossy(), 0)?;
    let source_path_string = path_string(&canonical_source_path, &std_root.to_string_lossy(), 0)?;
    let owner_name = runtime
        .module_manager
        .module(owner_module_id)
        .map(|module| module.module_name.clone())
        .unwrap_or_default();
    let local_name = package_name.to_string();
    let module_name = join_module_name(owner_name.as_str(), local_name.as_str());
    reject_active_mount_cycle(
        runtime,
        mount_stack,
        source_path_string.as_str(),
        module_name.as_str(),
        "cyclic standard package import",
        &canonical_source_path,
        0,
    )?;
    if let Some(existing_module_id) = runtime
        .module_manager
        .module_id_by_path(source_path_string.as_str())
    {
        return Ok(existing_module_id);
    }
    let module_id = runtime
        .module_manager
        .create_discovered_standard_module(
            module_name,
            source_path_string.clone(),
            source_path_string,
            ProjectHierarchy::Module,
            None,
        )
        .map_err(|message| {
            repository_error(message, &canonical_source_path.to_string_lossy(), 0)
        })?;
    Ok(module_id)
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

fn repository_targets_for_path(runtime: &Runtime, source_path: &str) -> Vec<RepositoryFileTarget> {
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

fn discover_module_config(
    runtime: &mut Runtime,
    module_id: ModuleId,
    config_path: &Path,
    config: ProjectConfig,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<(), RuntimeError> {
    let module_flatten = config.module_flatten;
    let module_flatten_line = config.module_flatten_line;
    let allow_bare_exports = config.allow_bare_exports.clone();
    let allow_bare_std_imports = config.allow_bare_std_imports.clone();
    let allow_bare_imports = config.allow_bare_imports.clone();
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
    validate_config_directory_contents(config_path, &config)?;
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
        let Some(ImportTarget::File { file_id, .. }) = module.run_targets.first().copied() else {
            return Err(repository_error(
                "[module] flatten requires exactly one exported file".to_string(),
                &config_path.to_string_lossy(),
                module_flatten_line.unwrap_or(config.hierarchy_line),
            ));
        };
        module.flattened_export_file = Some(file_id);
    }
    record_bare_symbol_sources(
        runtime,
        module_id,
        config_path,
        &allow_bare_exports,
        &allow_bare_std_imports,
        &allow_bare_imports,
    )?;
    Ok(())
}

fn record_bare_symbol_sources(
    runtime: &mut Runtime,
    module_id: ModuleId,
    config_path: &Path,
    allow_bare_exports: &[ProjectBareName],
    allow_bare_std_imports: &[ProjectBareName],
    allow_bare_imports: &[ProjectBareName],
) -> Result<(), RuntimeError> {
    let config_label: Rc<str> = Rc::from(config_path.to_string_lossy().to_string());
    let mut sources = Vec::new();
    {
        let module = runtime
            .module_manager
            .module(module_id)
            .expect("manifest owner module should exist");
        for allowed in allow_bare_exports {
            let target = module
                .exports
                .get(&allowed.name)
                .expect("allowed export was checked present")
                .target(module_id);
            if !matches!(target, ImportTarget::Module(_)) {
                return Err(repository_error(
                    format!(
                        "[allow bare export] `{}` must name an exported folder/submodule, not a .lit file",
                        allowed.name
                    ),
                    &config_path.to_string_lossy(),
                    allowed.line,
                ));
            }
            sources.push(ConfigBareSymbolSource {
                name: allowed.name.clone(),
                target,
                kind: BareSymbolSourceKind::Export,
                line_file: (allowed.line, config_label.clone()),
            });
        }
        for allowed in allow_bare_std_imports {
            let config_import = module
                .config_imports
                .iter()
                .find(|import| {
                    import.name == allowed.name && import.kind == ConfigImportKind::Standard
                })
                .expect("allowed standard import was checked present");
            sources.push(ConfigBareSymbolSource {
                name: allowed.name.clone(),
                target: ImportTarget::Module(config_import.module_id),
                kind: BareSymbolSourceKind::StandardImport,
                line_file: (allowed.line, config_label.clone()),
            });
        }
        for allowed in allow_bare_imports {
            let config_import = module
                .config_imports
                .iter()
                .find(|import| import.name == allowed.name && import.kind == ConfigImportKind::Path)
                .expect("allowed path import was checked present");
            sources.push(ConfigBareSymbolSource {
                name: allowed.name.clone(),
                target: ImportTarget::Module(config_import.module_id),
                kind: BareSymbolSourceKind::Import,
                line_file: (allowed.line, config_label.clone()),
            });
        }
    }
    runtime
        .module_manager
        .module_mut(module_id)
        .expect("manifest owner module should exist")
        .bare_symbol_sources = sources;
    Ok(())
}

fn reject_active_mount_cycle(
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
            .is_some_and(|module| module.module_root_path == child_root_path)
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

fn discover_config_import(
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
        PathBuf::from(&owner.module_root_path)
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
        .module_id_by_path(child_root_string.as_str())
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
            child_root_string,
            child_config_string,
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

fn discover_config_std_import(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    config_path: &Path,
    import: ProjectStdImport,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ConfigImport, RuntimeError> {
    let std_root = resolve_std_root().map_err(|message| {
        repository_error(message, &config_path.to_string_lossy(), import.line)
    })?;
    let std_module_id = discover_std_module_with_mount_stack(
        runtime,
        owner_module_id,
        &std_root,
        &import.name,
        mount_stack,
    )?;
    Ok(ConfigImport {
        name: import.name,
        module_id: std_module_id,
        kind: ConfigImportKind::Standard,
        line_file: (
            import.line,
            Rc::from(config_path.to_string_lossy().to_string()),
        ),
    })
}

fn append_config_import(runtime: &mut Runtime, module_id: ModuleId, config_import: ConfigImport) {
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

fn discover_config_export(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    config_path: &Path,
    export: ProjectExport,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ImportTarget, RuntimeError> {
    let (owner_root, owner_name) = {
        let owner = runtime
            .module_manager
            .module(owner_module_id)
            .expect("manifest owner module should exist");
        (
            PathBuf::from(&owner.module_root_path),
            owner.module_name.clone(),
        )
    };
    if runtime
        .module_manager
        .module(owner_module_id)
        .expect("manifest owner module should exist")
        .exports
        .contains_key(&export.name)
    {
        return Err(repository_error(
            format!("duplicate export name `{}` in [export]", export.name),
            &config_path.to_string_lossy(),
            export.line,
        ));
    }

    let child_name_on_disk = direct_child_name(
        export.path.as_str(),
        &config_path.to_string_lossy(),
        export.line,
        "[export]",
    )?;
    let target_path = owner_root.join(child_name_on_disk);
    if target_path.is_file() {
        let canonical_path =
            canonical_file(&target_path, &config_path.to_string_lossy(), export.line)?;
        if canonical_path.parent() != Some(owner_root.as_path()) {
            return Err(repository_error(
                "[export] file target must remain inside its containing folder".to_string(),
                &config_path.to_string_lossy(),
                export.line,
            ));
        }
        if canonical_path
            .extension()
            .and_then(|extension| extension.to_str())
            != Some("lit")
        {
            return Err(repository_error(
                "[export] file targets must point to a .lit file".to_string(),
                &config_path.to_string_lossy(),
                export.line,
            ));
        }
        let source_path =
            path_string(&canonical_path, &config_path.to_string_lossy(), export.line)?;
        let canonical_name = join_module_name(&owner_name, &export.name);
        let file_id = runtime
            .module_manager
            .module_mut(owner_module_id)
            .expect("manifest owner module should exist")
            .create_exported_file(source_path.clone(), canonical_name.clone());
        let target = ImportTarget::File {
            module_id: owner_module_id,
            file_id,
        };
        runtime
            .module_manager
            .register_exported_file(canonical_name, target)
            .map_err(|message| {
                repository_error(message, &config_path.to_string_lossy(), export.line)
            })?;
        runtime
            .module_manager
            .module_mut(owner_module_id)
            .expect("manifest owner module should exist")
            .exports
            .insert(
                export.name.clone(),
                ExportEntry::File {
                    name: export.name.clone(),
                    file_id,
                },
            );
        return Ok(target);
    } else if target_path.is_dir() {
        let canonical_root = canonical_directory(
            &target_path.to_string_lossy(),
            &config_path.to_string_lossy(),
            export.line,
        )?;
        if canonical_root.parent() != Some(owner_root.as_path()) {
            return Err(repository_error(
                "[export] folder target must remain inside its containing folder".to_string(),
                &config_path.to_string_lossy(),
                export.line,
            ));
        }
        let child_config_path =
            require_project_config(&canonical_root, &config_path.to_string_lossy(), export.line)?;
        let child_config = read_project_config(&child_config_path)?;
        if child_config.hierarchy != ProjectHierarchy::Submodule {
            return Err(repository_error(
                "[export] folder target must declare `submodule` under [hierarchy]".to_string(),
                &child_config_path.to_string_lossy(),
                child_config.hierarchy_line,
            ));
        }
        let child_name = join_module_name(&owner_name, &export.name);
        let child_root_string =
            path_string(&canonical_root, &config_path.to_string_lossy(), export.line)?;
        let child_config_string = path_string(
            &child_config_path,
            &config_path.to_string_lossy(),
            export.line,
        )?;
        reject_active_mount_cycle(
            runtime,
            mount_stack,
            child_root_string.as_str(),
            child_name.as_str(),
            "cyclic package export",
            config_path,
            export.line,
        )?;
        let child_module_id = runtime
            .module_manager
            .create_discovered_module(
                child_name,
                child_root_string,
                child_config_string,
                ProjectHierarchy::Submodule,
                Some(owner_module_id),
            )
            .map_err(|message| {
                repository_error(message, &config_path.to_string_lossy(), export.line)
            })?;
        let target = ImportTarget::Module(child_module_id);
        runtime
            .module_manager
            .module_mut(owner_module_id)
            .expect("manifest owner module should exist")
            .exports
            .insert(
                export.name.clone(),
                ExportEntry::Module {
                    name: export.name.clone(),
                    module_id: child_module_id,
                },
            );
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
        return Ok(target);
    } else {
        return Err(repository_error(
            format!(
                "[export] target `{}` does not exist",
                target_path.to_string_lossy()
            ),
            &config_path.to_string_lossy(),
            export.line,
        ));
    }
}

fn config_import_edges(runtime: &Runtime) -> HashMap<ModuleId, Vec<ModuleId>> {
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

fn reject_unauthorized_project_references(runtime: &Runtime) -> Result<(), RuntimeError> {
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

fn collect_project_reference_targets(
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

fn project_target_is_authorized_for_module(
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

fn target_belongs_to_export_tree(
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

fn reject_cyclic_module_imports(
    runtime: &Runtime,
    edges: &HashMap<ModuleId, Vec<ModuleId>>,
) -> Result<(), RuntimeError> {
    let mut visited = HashSet::new();
    let mut visiting = HashSet::new();
    let mut stack = vec![];
    for module_id in edges.keys().copied().collect::<Vec<ModuleId>>() {
        if let Some(cycle) =
            find_module_import_cycle(module_id, edges, &mut visited, &mut visiting, &mut stack)
        {
            let names = cycle
                .iter()
                .map(|cycle_id| {
                    runtime
                        .module_manager
                        .module(*cycle_id)
                        .map(|module| {
                            if module.module_name.is_empty() {
                                "<root>".to_string()
                            } else {
                                module.module_name.clone()
                            }
                        })
                        .unwrap_or_else(|| format!("module#{}", cycle_id.0))
                })
                .collect::<Vec<String>>();
            let source_path = runtime
                .module_manager
                .module(module_id)
                .map(|module| module.main_file_path.as_str())
                .unwrap_or("");
            return Err(repository_error(
                format!("cyclic module import: {}", names.join(" -> ")),
                source_path,
                0,
            ));
        }
    }
    Ok(())
}

fn find_module_import_cycle(
    module_id: ModuleId,
    edges: &HashMap<ModuleId, Vec<ModuleId>>,
    visited: &mut HashSet<ModuleId>,
    visiting: &mut HashSet<ModuleId>,
    stack: &mut Vec<ModuleId>,
) -> Option<Vec<ModuleId>> {
    if visited.contains(&module_id) {
        return None;
    }
    if visiting.contains(&module_id) {
        let start = stack
            .iter()
            .position(|item| *item == module_id)
            .unwrap_or(0);
        let mut cycle = stack[start..].to_vec();
        cycle.push(module_id);
        return Some(cycle);
    }

    visiting.insert(module_id);
    stack.push(module_id);
    if let Some(dependencies) = edges.get(&module_id) {
        for dependency in dependencies {
            if let Some(cycle) =
                find_module_import_cycle(*dependency, edges, visited, visiting, stack)
            {
                return Some(cycle);
            }
        }
    }
    stack.pop();
    visiting.remove(&module_id);
    visited.insert(module_id);
    None
}

fn canonical_directory(
    path: &str,
    source_path: &str,
    line: usize,
) -> Result<PathBuf, RuntimeError> {
    let canonical = fs::canonicalize(path).map_err(|error| {
        repository_error(
            format!("module directory `{}` does not exist: {}", path, error),
            source_path,
            line,
        )
    })?;
    if !canonical.is_dir() {
        return Err(repository_error(
            format!("module path `{}` is not a directory", path),
            source_path,
            line,
        ));
    }
    Ok(canonical)
}

fn canonical_file(path: &Path, source_path: &str, line: usize) -> Result<PathBuf, RuntimeError> {
    let canonical = fs::canonicalize(path).map_err(|error| {
        repository_error(
            format!(
                "source file `{}` does not exist: {}",
                path.to_string_lossy(),
                error
            ),
            source_path,
            line,
        )
    })?;
    if !canonical.is_file() {
        return Err(repository_error(
            format!(
                "configured source path `{}` is not a file",
                path.to_string_lossy()
            ),
            source_path,
            line,
        ));
    }
    Ok(canonical)
}

fn require_project_config(
    directory: &Path,
    source_path: &str,
    line: usize,
) -> Result<PathBuf, RuntimeError> {
    let config_path = directory.join(LITEX_CONFIG);
    require_file(
        &config_path,
        format!(
            "project directory `{}` does not contain {}",
            directory.to_string_lossy(),
            LITEX_CONFIG
        ),
        source_path,
        line,
    )?;
    Ok(config_path)
}

fn read_project_config(config_path: &Path) -> Result<ProjectConfig, RuntimeError> {
    let config_path_string = path_string(config_path, &config_path.to_string_lossy(), 0)?;
    let content = fs::read_to_string(config_path).map_err(|error| {
        repository_error(
            format!(
                "failed to read {}: {}",
                config_path.to_string_lossy(),
                error
            ),
            config_path_string.as_str(),
            0,
        )
    })?;
    parse_project_config(content.as_str(), config_path_string.as_str())
}

fn require_file(
    path: &Path,
    message: String,
    source_path: &str,
    line: usize,
) -> Result<(), RuntimeError> {
    if path.is_file() {
        Ok(())
    } else {
        Err(repository_error(message, source_path, line))
    }
}

fn path_string(path: &Path, source_path: &str, line: usize) -> Result<String, RuntimeError> {
    path.to_str().map(str::to_string).ok_or_else(|| {
        repository_error(
            "repository path is not valid UTF-8".to_string(),
            source_path,
            line,
        )
    })
}

fn enclosing_module_root(
    requested_root: &Path,
    requested_config_path: &Path,
    requested_config: &ProjectConfig,
    source_path: &str,
) -> Result<PathBuf, RuntimeError> {
    let mut current_root = requested_root.to_path_buf();
    let mut current_config_path = requested_config_path.to_path_buf();
    let mut current_config = requested_config.clone();
    loop {
        if current_config.hierarchy == ProjectHierarchy::Module {
            reject_module_with_configured_parent(
                &current_root,
                &current_config_path,
                &current_config,
            )?;
            return Ok(current_root);
        }
        let parent = current_root.parent().ok_or_else(|| {
            repository_error(
                "submodule hierarchy reached the filesystem root without finding a module"
                    .to_string(),
                source_path,
                current_config.hierarchy_line,
            )
        })?;
        let parent_config_path = require_project_config(
            parent,
            &current_config_path.to_string_lossy(),
            current_config.hierarchy_line,
        )?;
        let parent_config = read_project_config(&parent_config_path)?;
        let current_name = current_root
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| {
                repository_error(
                    "submodule folder name is not valid UTF-8".to_string(),
                    &current_config_path.to_string_lossy(),
                    current_config.hierarchy_line,
                )
            })?;
        let exported_by_parent = parent_config.exports.iter().any(|export| {
            direct_child_name(
                export.path.as_str(),
                &parent_config_path.to_string_lossy(),
                export.line,
                "[export]",
            )
            .is_ok_and(|name| name == current_name)
        });
        if !exported_by_parent {
            return Err(repository_error(
                format!(
                    "submodule folder `{}` is not directly exported by its parent litex.config",
                    current_root.to_string_lossy()
                ),
                &current_config_path.to_string_lossy(),
                current_config.hierarchy_line,
            ));
        }
        current_root = parent.to_path_buf();
        current_config_path = parent_config_path;
        current_config = parent_config;
    }
}

fn reject_module_with_configured_parent(
    module_root: &Path,
    config_path: &Path,
    config: &ProjectConfig,
) -> Result<(), RuntimeError> {
    if module_root
        .parent()
        .is_some_and(|parent| parent.join(LITEX_CONFIG).is_file())
    {
        return Err(repository_error(
            "a [hierarchy] module cannot have a configured parent folder".to_string(),
            &config_path.to_string_lossy(),
            config.hierarchy_line,
        ));
    }
    Ok(())
}

fn validate_config_directory_contents(
    config_path: &Path,
    config: &ProjectConfig,
) -> Result<(), RuntimeError> {
    let root = config_path.parent().ok_or_else(|| {
        repository_error(
            "litex.config has no containing folder".to_string(),
            &config_path.to_string_lossy(),
            0,
        )
    })?;
    let mut exported_children = HashMap::new();
    for export in config.exports.iter() {
        let child_name = direct_child_name(
            export.path.as_str(),
            &config_path.to_string_lossy(),
            export.line,
            "[export]",
        )?;
        if let Some(previous_line) = exported_children.insert(child_name.clone(), export.line) {
            return Err(repository_error(
                format!(
                    "[export] path `{}` is declared more than once (first declared on line {})",
                    child_name, previous_line
                ),
                &config_path.to_string_lossy(),
                export.line,
            ));
        }
    }
    let entries = fs::read_dir(root).map_err(|error| {
        repository_error(
            format!(
                "failed to inspect configured folder `{}`: {}",
                root.to_string_lossy(),
                error
            ),
            &config_path.to_string_lossy(),
            0,
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|error| {
            repository_error(
                format!("failed to inspect configured folder entry: {}", error),
                &config_path.to_string_lossy(),
                0,
            )
        })?;
        let name = entry.file_name().to_string_lossy().into_owned();
        let path = entry.path();
        if name == LITEX_CONFIG {
            continue;
        }
        // Local work records are outside the ordered, publishable module tree.
        if name == LOCAL_DRAFTS {
            continue;
        }
        if name == LITEX_TODO {
            let source = fs::read_to_string(&path).map_err(|error| {
                repository_error(
                    format!("failed to read todo.lit: {}", error),
                    &path.to_string_lossy(),
                    0,
                )
            })?;
            let source_without_documentation =
                Tokenizer::new().strip_triple_quote_comment_blocks(&source);
            if let Some(line) = source_without_documentation
                .lines()
                .position(|line| !line.trim().is_empty() && !line.trim().starts_with('#'))
            {
                return Err(repository_error(
                    "todo.lit must be comment-only".to_string(),
                    &path.to_string_lossy(),
                    line + 1,
                ));
            }
            continue;
        }
        let is_litex_source =
            path.extension().and_then(|extension| extension.to_str()) == Some("lit");
        if !path.is_dir() && !is_litex_source {
            continue;
        }
        if !exported_children.contains_key(&name) {
            return Err(repository_error(
                format!(
                    "configured folder contains unexported Litex module path `{}`; every direct child directory or .lit file must appear in [export]",
                    name
                ),
                &config_path.to_string_lossy(),
                0,
            ));
        }
    }
    Ok(())
}

fn direct_child_name(
    configured_path: &str,
    source_path: &str,
    line: usize,
    table: &str,
) -> Result<String, RuntimeError> {
    let mut child_name = None;
    for component in Path::new(configured_path).components() {
        match component {
            Component::CurDir => {}
            Component::Normal(name) if child_name.is_none() => {
                child_name = name.to_str().map(str::to_string);
            }
            _ => {
                return Err(repository_error(
                    format!("{} paths must name exactly one direct child", table),
                    source_path,
                    line,
                ))
            }
        }
    }
    child_name.ok_or_else(|| {
        repository_error(
            format!("{} paths must name exactly one direct child", table),
            source_path,
            line,
        )
    })
}

fn join_module_name(parent: &str, child: &str) -> String {
    if parent.is_empty() {
        child.to_string()
    } else {
        format!("{}{}{}", parent, MOD_SIGN, child)
    }
}

fn repository_error(message: String, source_path: &str, line: usize) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message,
        (line, Rc::from(source_path)),
    ))
    .into()
}

fn terminal_import_target_path(
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

fn standard_library_root_candidates(
    configured_root: Option<PathBuf>,
    current_dir: Option<PathBuf>,
    executable: Option<PathBuf>,
) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    if let Some(root) = configured_root {
        roots.push(root);
    }
    if let Some(dir) = current_dir {
        roots.push(dir.join("std"));
    }
    if let Some(parent) = executable.as_deref().and_then(Path::parent) {
        roots.push(parent.join("std"));
        roots.push(parent.join("..").join("std"));
        roots.push(parent.join("..").join("share").join("litex").join("std"));
        roots.push(
            parent
                .join("..")
                .join("..")
                .join("share")
                .join("litex")
                .join("std"),
        );
    }
    roots
}

#[cfg(test)]
#[path = "../../tests/unit/module_manager/repository/tests.rs"]
mod tests;
