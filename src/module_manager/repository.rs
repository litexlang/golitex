use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

const LITEX_CONFIG: &str = "litex.config";

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
) -> Result<String, RuntimeError> {
    let repository_root = canonical_directory(repository_path, repository_path, 0)?;
    let config_path = require_project_config(&repository_root, repository_path, 0)?;
    let config = read_project_config(&config_path)?;
    let repository_root_string = path_string(&repository_root, repository_path, 0)?;
    let config_path_string = path_string(&config_path, repository_path, 0)?;
    let root_module_id = runtime
        .new_repository_path_new_env_new_name_scope(
            repository_root_string,
            config_path_string.clone(),
        )
        .map_err(|message| repository_error(message, repository_path, 0))?;

    let mut mount_stack = vec![root_module_id];
    discover_module_config(
        runtime,
        root_module_id,
        &config_path,
        config,
        true,
        &mut mount_stack,
    )?;
    reject_unauthorized_project_references(runtime)?;
    let module_import_edges = config_import_edges(runtime);
    reject_cyclic_module_imports(runtime, &module_import_edges)?;
    Ok(config_path_string)
}

pub fn discover_std_module(
    runtime: &mut Runtime,
    std_root: &Path,
    package_name: &str,
) -> Result<ModuleId, RuntimeError> {
    let mut mount_stack = vec![];
    discover_std_module_with_mount_stack(runtime, std_root, package_name, &mut mount_stack)
}

pub fn resolve_std_root() -> Result<PathBuf, String> {
    let configured_root = env::var("LITEX_STD_PATH").ok().map(PathBuf::from);
    let current_dir = env::current_dir().ok();
    let executable = env::current_exe().ok();
    for root in standard_library_root_candidates(configured_root, current_dir, executable) {
        if root.join(LITEX_CONFIG).is_file() {
            return Ok(root);
        }
    }
    Err("standard library was not found; searched LITEX_STD_PATH, ./std, and the executable installation paths".to_string())
}

fn discover_std_module_with_mount_stack(
    runtime: &mut Runtime,
    std_root: &Path,
    package_name: &str,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ModuleId, RuntimeError> {
    let canonical_std_root =
        canonical_directory(&std_root.to_string_lossy(), &std_root.to_string_lossy(), 0)?;
    let config_path = require_project_config(
        &canonical_std_root,
        &canonical_std_root.to_string_lossy(),
        0,
    )?;
    let config = read_project_config(&config_path)?;
    let std_root_string = path_string(&canonical_std_root, &config_path.to_string_lossy(), 0)?;
    let config_path_string = path_string(&config_path, &config_path.to_string_lossy(), 0)?;
    let std_module_id = match runtime.module_manager.module_id_by_name("std") {
        Some(module_id) => {
            let existing_root = runtime
                .module_manager
                .module(module_id)
                .map(|module| module.module_root_path.clone())
                .unwrap_or_default();
            if existing_root != std_root_string {
                return Err(repository_error(
                    format!(
                        "standard library root `{}` conflicts with module `std` at `{}`",
                        std_root_string, existing_root
                    ),
                    &config_path.to_string_lossy(),
                    0,
                ));
            }
            module_id
        }
        None => runtime
            .module_manager
            .create_discovered_module("std".to_string(), std_root_string, config_path_string)
            .map_err(|message| repository_error(message, &config_path.to_string_lossy(), 0))?,
    };
    if mount_stack.contains(&std_module_id) {
        return Err(repository_error(
            "cyclic config import involving `std`".to_string(),
            &config_path.to_string_lossy(),
            0,
        ));
    }
    let selected_config = select_project_exports(&config, &[package_name], &config_path)?;
    mount_stack.push(std_module_id);
    let discovery = discover_module_config(
        runtime,
        std_module_id,
        &config_path,
        selected_config,
        true,
        mount_stack,
    );
    mount_stack.pop();
    discovery?;
    Ok(std_module_id)
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
    let canonical_file_string = path_string(&canonical_file, file_path, 0)?;
    let mut roots = canonical_file
        .parent()
        .into_iter()
        .flat_map(Path::ancestors)
        .filter(|directory| directory.join(LITEX_CONFIG).is_file())
        .collect::<Vec<&Path>>();
    roots.reverse();
    for root in roots {
        let root_string = path_string(root, file_path, 0)?;
        let mut probe = Runtime::new();
        if discover_repository(&mut probe, root_string.as_str()).is_err() {
            continue;
        }
        let targets = repository_targets_for_path(&probe, canonical_file_string.as_str());
        if targets.is_empty() {
            continue;
        }
        if targets.len() > 1 {
            return Err(repository_error(
                format!(
                    "source file `{}` is mounted more than once by this repository; run a repository entry point instead of this physical path",
                    canonical_file_string
                ),
                file_path,
                0,
            ));
        }
        discover_repository(runtime, root_string.as_str())?;
        return Ok(
            repository_targets_for_path(runtime, canonical_file_string.as_str())
                .into_iter()
                .next(),
        );
    }
    Ok(None)
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
    allow_config_imports: bool,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<(), RuntimeError> {
    if config.module_flatten && runtime.module_manager.entry_module_id == Some(module_id) {
        return Err(repository_error(
            "[module] flatten = true requires a named module; it cannot be used by the direct repository root".to_string(),
            &config_path.to_string_lossy(),
            config.module_flatten_line.unwrap_or(0),
        ));
    }
    if !allow_config_imports && (!config.imports.is_empty() || !config.std_imports.is_empty()) {
        let line = config
            .imports
            .first()
            .map(|import| import.line)
            .or_else(|| config.std_imports.first().map(|import| import.line))
            .unwrap_or(0);
        return Err(repository_error(
            "only a repository root or an independently imported package may use [import] or [import std]".to_string(),
            &config_path.to_string_lossy(),
            line,
        ));
    }
    for import in config.imports.iter().cloned() {
        let config_import =
            discover_config_import(runtime, module_id, config_path, import, mount_stack)?;
        append_config_import(runtime, module_id, config_import);
    }
    for import in config.std_imports.iter().cloned() {
        let config_import = discover_config_std_import(runtime, config_path, import, mount_stack)?;
        append_config_import(runtime, module_id, config_import);
    }

    let module_flatten = config.module_flatten;
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
        let trusted = export.trusted;
        let line_file = (
            export.line,
            Rc::from(config_path.to_string_lossy().to_string()),
        );
        let target = discover_config_export(
            runtime,
            module_id,
            config_path,
            export,
            module_flatten,
            mount_stack,
        )?;
        let module = runtime
            .module_manager
            .module_mut(module_id)
            .expect("manifest owner module should exist");
        module.run_targets.push(target);
        if trusted {
            module.trusted_run_targets.insert(target, line_file);
        }
    }

    for requirement in config.requirements {
        let (target, dependencies) = {
            let module = runtime
                .module_manager
                .module(module_id)
                .expect("manifest owner module should exist");
            let target = module
                .exports
                .get(&requirement.name)
                .expect("parsed [requires] target should be exported")
                .target(module_id);
            let dependencies = requirement
                .dependencies
                .iter()
                .map(|dependency| {
                    module
                        .exports
                        .get(dependency)
                        .expect("parsed [requires] dependency should be exported")
                        .target(module_id)
                })
                .collect::<Vec<ImportTarget>>();
            (target, dependencies)
        };
        runtime
            .module_manager
            .module_mut(module_id)
            .expect("manifest owner module should exist")
            .required_targets
            .insert(target, dependencies);
    }
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
    // An [import] grants a package capability; unlike [export], it does not
    // make the imported package a lexical child of its owner.  Thus an import
    // named B is B, while B's exported F is B::F.
    let child_name = import.name.clone();
    reject_active_mount_cycle(
        runtime,
        mount_stack,
        child_root_string.as_str(),
        child_name.as_str(),
        "cyclic config import",
        config_path,
        import.line,
    )?;
    if let Some(existing_module_id) = runtime.module_manager.module_id_by_name(&child_name) {
        let existing_root = runtime
            .module_manager
            .module(existing_module_id)
            .map(|module| module.module_root_path.clone())
            .unwrap_or_default();
        if existing_root == child_root_string {
            return Ok(ConfigImport {
                module_id: existing_module_id,
                line_file: (
                    import.line,
                    Rc::from(config_path.to_string_lossy().to_string()),
                ),
                trusted: import.trusted,
            });
        }
        return Err(repository_error(
            format!(
                "[import] name `{}` is already bound to package path `{}`",
                child_name, existing_root
            ),
            &config_path.to_string_lossy(),
            import.line,
        ));
    }
    let child_config = read_project_config(&child_config_path)?;
    let child_module_id = runtime
        .module_manager
        .create_discovered_module(child_name, child_root_string, child_config_string)
        .map_err(|message| {
            repository_error(message, &config_path.to_string_lossy(), import.line)
        })?;
    mount_stack.push(child_module_id);
    let discovery = discover_module_config(
        runtime,
        child_module_id,
        &child_config_path,
        child_config,
        true,
        mount_stack,
    );
    mount_stack.pop();
    discovery?;
    Ok(ConfigImport {
        module_id: child_module_id,
        line_file: (
            import.line,
            Rc::from(config_path.to_string_lossy().to_string()),
        ),
        trusted: import.trusted,
    })
}

fn discover_config_std_import(
    runtime: &mut Runtime,
    config_path: &Path,
    import: ProjectStdImport,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ConfigImport, RuntimeError> {
    let std_root = resolve_std_root().map_err(|message| {
        repository_error(message, &config_path.to_string_lossy(), import.line)
    })?;
    let std_module_id =
        discover_std_module_with_mount_stack(runtime, &std_root, &import.name, mount_stack)?;
    Ok(ConfigImport {
        module_id: std_module_id,
        line_file: (
            import.line,
            Rc::from(config_path.to_string_lossy().to_string()),
        ),
        trusted: false,
    })
}

fn append_config_import(runtime: &mut Runtime, module_id: ModuleId, config_import: ConfigImport) {
    let module = runtime
        .module_manager
        .module_mut(module_id)
        .expect("manifest owner module should exist");
    if module.config_imports.iter().any(|existing| {
        existing.module_id == config_import.module_id && existing.trusted == config_import.trusted
    }) {
        return;
    }
    module.config_imports.push(config_import);
}

fn select_project_exports(
    config: &ProjectConfig,
    requested_export_names: &[&str],
    config_path: &Path,
) -> Result<ProjectConfig, RuntimeError> {
    let mut selected_names = HashSet::new();
    let mut pending_names = requested_export_names
        .iter()
        .map(|name| (*name).to_string())
        .collect::<Vec<String>>();

    while let Some(name) = pending_names.pop() {
        if !selected_names.insert(name.clone()) {
            continue;
        }
        let Some(export) = config.exports.iter().find(|export| export.name == name) else {
            return Err(repository_error(
                format!("[export] target `{}` is not declared", name),
                &config_path.to_string_lossy(),
                0,
            ));
        };
        if let Some(requirement) = config
            .requirements
            .iter()
            .find(|requirement| requirement.name == export.name)
        {
            pending_names.extend(requirement.dependencies.iter().cloned());
        }
    }

    let mut selected_config = config.clone();
    selected_config.exports = config
        .exports
        .iter()
        .filter(|export| selected_names.contains(&export.name))
        .cloned()
        .collect();
    selected_config.requirements = config
        .requirements
        .iter()
        .filter(|requirement| selected_names.contains(&requirement.name))
        .cloned()
        .collect();
    Ok(selected_config)
}

fn discover_config_export(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    config_path: &Path,
    export: ProjectExport,
    module_flatten: bool,
    mount_stack: &mut Vec<ModuleId>,
) -> Result<ImportTarget, RuntimeError> {
    let (owner_root, owner_name, is_root) = {
        let owner = runtime
            .module_manager
            .module(owner_module_id)
            .expect("manifest owner module should exist");
        (
            PathBuf::from(&owner.module_root_path),
            owner.module_name.clone(),
            runtime.module_manager.entry_module_id == Some(owner_module_id),
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

    let target_path = owner_root.join(&export.path);
    if target_path.is_file() {
        let canonical_path =
            canonical_file(&target_path, &config_path.to_string_lossy(), export.line)?;
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
        let canonical_name = if module_flatten {
            owner_name.clone()
        } else {
            join_module_name(&owner_name, &export.name)
        };
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
            .register_exported_file(canonical_name, source_path, target)
            .map_err(|message| {
                repository_error(message, &config_path.to_string_lossy(), export.line)
            })?;
        if module_flatten {
            runtime
                .module_manager
                .module_mut(owner_module_id)
                .expect("manifest owner module should exist")
                .flattened_export_file = Some(file_id);
        }
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
        if is_root {
            runtime
                .module_manager
                .register_root_export(export.name, target)
                .map_err(|message| {
                    repository_error(message, &config_path.to_string_lossy(), export.line)
                })?;
        }
        return Ok(target);
    } else if target_path.is_dir() {
        if module_flatten {
            return Err(repository_error(
                "[module] flatten = true requires its only [export] entry to point directly to a .lit file".to_string(),
                &config_path.to_string_lossy(),
                export.line,
            ));
        }
        let canonical_root = canonical_directory(
            &target_path.to_string_lossy(),
            &config_path.to_string_lossy(),
            export.line,
        )?;
        let child_config_path =
            require_project_config(&canonical_root, &config_path.to_string_lossy(), export.line)?;
        let child_config = read_project_config(&child_config_path)?;
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
            .create_discovered_module(child_name, child_root_string, child_config_string)
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
        if is_root {
            runtime
                .module_manager
                .register_root_export(export.name, target)
                .map_err(|message| {
                    repository_error(message, &config_path.to_string_lossy(), export.line)
                })?;
        }
        mount_stack.push(child_module_id);
        let discovery = discover_module_config(
            runtime,
            child_module_id,
            &child_config_path,
            child_config,
            false,
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

fn config_import_edges(runtime: &mut Runtime) -> HashMap<ModuleId, Vec<ModuleId>> {
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
        module_import_edges.insert(module_id, imported_modules.clone());
        let module = runtime
            .module_manager
            .module_mut(module_id)
            .expect("discovered module should exist");
        for imported_module in imported_modules {
            module.record_import(imported_module);
        }
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
        let mut tokenizer = Tokenizer::new();
        let blocks = tokenizer.parse_blocks(&source, Rc::from(source_path.as_str()))?;
        let mut references = vec![];
        collect_project_reference_targets(runtime, blocks.as_slice(), &mut references);
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
    blocks: &[TokenBlock],
    references: &mut Vec<(ImportTarget, LineFile)>,
) {
    for block in blocks {
        for start in 0..block.header.len() {
            if start > 0 && block.header[start - 1] == MOD_SIGN {
                continue;
            }
            let mut candidate = block.header[start].clone();
            let mut index = start;
            let mut longest_match = runtime
                .module_manager
                .import_target_by_canonical_name(candidate.as_str());
            while block.header.get(index + 1).map(String::as_str) == Some(MOD_SIGN) {
                let Some(next) = block.header.get(index + 2) else {
                    break;
                };
                candidate = format!("{}{}{}", candidate, MOD_SIGN, next);
                index += 2;
                if let Some(target) = runtime
                    .module_manager
                    .import_target_by_canonical_name(candidate.as_str())
                {
                    longest_match = Some(target);
                }
            }
            if let Some(target) = longest_match {
                if !references.iter().any(|(known, _)| *known == target) {
                    references.push((target, block.line_file.clone()));
                }
            }
        }
        collect_project_reference_targets(runtime, block.body.as_slice(), references);
    }
}

fn project_target_is_authorized_for_module(
    runtime: &Runtime,
    owner_module_id: ModuleId,
    target: ImportTarget,
) -> bool {
    if target_belongs_to_export_tree(runtime, owner_module_id, target) {
        return true;
    }
    let owner_name = runtime
        .module_manager
        .module(owner_module_id)
        .map(|module| module.module_name.clone())
        .unwrap_or_default();
    for module in runtime.module_manager.modules.values() {
        if !module_is_ancestor_of(module.module_name.as_str(), owner_name.as_str()) {
            continue;
        }
        for config_import in module.config_imports.iter() {
            if target_belongs_to_module_name(runtime, target, config_import.module_id) {
                return true;
            }
        }
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
        entry == target || matches!(entry, ImportTarget::Module(module_id) if target_belongs_to_module_name(runtime, target, module_id))
    })
}

fn target_belongs_to_module_name(
    runtime: &Runtime,
    target: ImportTarget,
    module_id: ModuleId,
) -> bool {
    let Some(module) = runtime.module_manager.module(module_id) else {
        return false;
    };
    let Some(target_name) = runtime.module_manager.canonical_name_for_target(target) else {
        return false;
    };
    target_name == module.module_name
        || target_name
            .strip_prefix(module.module_name.as_str())
            .is_some_and(|suffix| suffix.starts_with(MOD_SIGN))
}

fn module_is_ancestor_of(ancestor_name: &str, module_name: &str) -> bool {
    ancestor_name.is_empty()
        || ancestor_name == module_name
        || module_name
            .strip_prefix(ancestor_name)
            .is_some_and(|suffix| suffix.starts_with(MOD_SIGN))
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
mod tests {
    use super::*;

    const LARGE_REPOSITORY_TEST_STACK_SIZE: usize = 64 * 1024 * 1024;

    #[test]
    fn ordered_exports_use_canonical_namespaces() {
        run_repository_test_with_large_stack("repository_exports", || {
            let root = repository_test_dir("exports");
            let a = root.join("A");
            let chapters = a.join("chapters");
            fs::create_dir_all(&chapters).expect("create repository fixture");
            write_file(
                &root.join("litex.config"),
                "[import]\nA = \"./A\"\n\n[export]\nbefore = \"./before.lit\"\nmain = \"./main.lit\"\n",
            );
            write_file(&root.join("before.lit"), "have before R = 1\n");
            write_file(&root.join("main.lit"), "A::chapters::leaf::x = 1\n");
            write_project_config(
                &a,
                "./main.lit",
                &[
                    ("chap2", "./chap2.lit"),
                    ("chap3", "./chap3.lit"),
                    ("chapters", "./chapters"),
                ],
            );
            write_file(&a.join("main.lit"), "A::chap3::z = 1\n");
            write_file(&a.join("chap2.lit"), "have x R = 1\n");
            write_file(&a.join("chap3.lit"), "have z R = A::chap2::x\n");
            write_project_config(&chapters, "./main.lit", &[("leaf", "./leaf.lit")]);
            write_file(&chapters.join("main.lit"), "A::chapters::leaf::x = 1\n");
            write_file(&chapters.join("leaf.lit"), "have x R = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
            assert!(output.contains("A::chapters::leaf::x = 1"), "{output}");

            let (chapter_ok, chapter_output) = run_source_code_in_file_with_ok(
                a.join("chap3.lit").to_str().expect("fixture path is UTF-8"),
            );
            assert!(chapter_ok, "{chapter_output}");
            assert!(chapter_output.contains("have x R = 1"), "{chapter_output}");
        });
    }

    #[test]
    fn earlier_exports_require_explicit_member_names() {
        run_repository_test_with_large_stack("repository_explicit_members", || {
            let root = repository_test_dir("explicit-local-members");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_project_config(&root, "./main.lit", &[("member", "./member.lit")]);
            write_file(
                &root.join("member.lit"),
                "have value R = 1\n\nprop marked(x R):\n    x = x\n\nthm exported:\n    ? forall x R:\n        x = x\n    x = x\n",
            );

            write_file(&root.join("main.lit"), "value = 1\n");
            let (object_ok, object_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!object_ok, "{object_output}");
            assert!(object_output.contains("not defined"), "{object_output}");

            write_file(&root.join("main.lit"), "$marked(1)\n");
            let (predicate_ok, predicate_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!predicate_ok, "{predicate_output}");
            assert!(
                predicate_output.contains("not defined"),
                "{predicate_output}"
            );

            write_file(
                &root.join("main.lit"),
                "thm use_exported:\n    ? forall x R:\n        x = x\n    by thm exported(x)\n",
            );
            let (theorem_ok, theorem_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!theorem_ok, "{theorem_output}");
            assert!(theorem_output.contains("not defined"), "{theorem_output}");

            write_file(
                &root.join("main.lit"),
                "member::value = 1\n$member::marked(1)\n\nthm use_exported:\n    ? forall x R:\n        x = x\n    by thm member::exported(x)\n",
            );
            let (explicit_ok, explicit_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(explicit_ok, "{explicit_output}");
        });
    }

    #[test]
    fn repository_imported_cart_definition_retains_dimension_and_projections() {
        run_repository_test_with_large_stack("repository_imported_cart_definition", || {
            let root = repository_test_dir("imported-cart-definition");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_project_config(&root, "./main.lit", &[("geometry", "./geometry.lit")]);
            write_file(
                &root.join("geometry.lit"),
                "have n N_pos = 3\n\nhave cart C for i <= n, proj(C, i) = R\n",
            );
            write_file(
                &root.join("main.lit"),
                "$is_cart(geometry::C)\ncart_dim(geometry::C) = 3\nforall i closed_range(1, 3):\n    proj(geometry::C, i) = R\n",
            );

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
        });
    }

    #[test]
    fn repository_imported_casewise_have_fn_expands_every_case() {
        run_repository_test_with_large_stack("repository_imported_casewise_have_fn", || {
            let root = repository_test_dir("imported-casewise-have-fn");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_project_config(&root, "./main.lit", &[("branch", "./branch.lit")]);
            write_file(
                &root.join("branch.lit"),
                "have fn previous(x R) R = x\n\nhave fn select(x R) R by cases:\n    case x < 0: -1\n    case x >= 0: previous(x)\n",
            );
            write_file(
                &root.join("main.lit"),
                "branch::previous(0) = 0\nbranch::select(0) = branch::previous(0)\n",
            );

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
        });
    }

    #[test]
    fn repository_example_works_across_output_frontends() {
        run_repository_test_with_large_stack("repository_frontends", || {
            let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("examples")
                .join("08_module_repository");
            let repository_path = root.to_str().expect("example path is UTF-8");

            let (verifier_ok, verifier_output) = run_repository_with_output(
                repository_path,
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(verifier_ok, "{verifier_output}");
            assert!(verifier_output.contains("A::chap3::z = 1"));

            let (runner_ok, runner_output) = run_runner_for_repo(repository_path, true);
            assert!(runner_ok, "{runner_output}");

            let (graph_ok, graph_output) = run_graph_for_repo(repository_path, true);
            assert!(graph_ok, "{graph_output}");

            let latex_output = crate::to_latex::to_latex_from_repository(repository_path)
                .unwrap_or_else(|error| panic!("repository LaTeX failed: {error:?}"));
            assert!(latex_output.contains("A::chap3"), "{latex_output}");

            let python_output = crate::to_python::to_python_from_repository(repository_path)
                .unwrap_or_else(|error| panic!("repository Python failed: {error:?}"));
            assert_eq!(python_output, "x = 1.0\nz = 1.0\nanswer = 1.0");

            let chapter_path = root.join("A").join("chap3.lit");
            let chapter_path_string = chapter_path.to_str().expect("chapter path is UTF-8");
            let (chapter_ok, chapter_output) = run_source_code_in_file_with_ok(chapter_path_string);
            assert!(chapter_ok, "{chapter_output}");
            assert!(chapter_output.contains("have x R = 1"), "{chapter_output}");
            assert!(chapter_output.contains("A::chap2::x"), "{chapter_output}");

            let (chapter_runner_ok, chapter_runner_output) =
                run_runner_for_file(chapter_path_string, true);
            assert!(chapter_runner_ok, "{chapter_runner_output}");

            let (chapter_graph_ok, chapter_graph_output) =
                run_graph_for_file(chapter_path_string, true);
            assert!(chapter_graph_ok, "{chapter_graph_output}");

            let chapter_latex = crate::to_latex::to_latex_from_file(chapter_path_string)
                .unwrap_or_else(|error| panic!("project chapter LaTeX failed: {error:?}"));
            assert!(chapter_latex.contains("chap2"), "{chapter_latex}");

            let mut isolated_runtime = Runtime::new();
            let (_, isolated_error) = crate::pipeline::run_file_with_project_context(
                chapter_path_string,
                &mut isolated_runtime,
                true,
            );
            assert!(
                isolated_error.is_some(),
                "isolated mode must not load chap2"
            );
        });
    }

    #[test]
    fn later_exports_are_not_visible_to_earlier_files() {
        run_repository_test_with_large_stack("repository_order", || {
            let root = repository_test_dir("cycle");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_project_config(&root, "./main.lit", &[("a", "./a.lit"), ("b", "./b.lit")]);
            write_file(&root.join("main.lit"), "a::x = 1\n");
            write_file(&root.join("a.lit"), "b::x = 1\n");
            write_file(&root.join("b.lit"), "have x R = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                true,
                OutputLanguage::English,
                false,
            );
            assert!(!ok, "{output}");
            assert!(output.contains("identifier `b::x` not defined"), "{output}");
        });
    }

    #[test]
    fn repository_discovery_reports_module_cycles_separately() {
        run_repository_test_with_large_stack("repository_module_cycle", || {
            let root = repository_test_dir("module-cycle");
            let a = root.join("A");
            let b = root.join("B");
            fs::create_dir_all(&a).expect("create A fixture");
            fs::create_dir_all(&b).expect("create B fixture");
            write_file(
                &root.join("litex.config"),
                "[import]\nA = \"./A\"\n\n[export]\nmain = \"./main.lit\"\n",
            );
            write_file(&root.join("main.lit"), "1 = 1\n");
            write_file(
                &a.join("litex.config"),
                "[import]\nB = \"../B\"\n\n[export]\nmain = \"./main.lit\"\n",
            );
            write_file(&a.join("main.lit"), "1 = 1\n");
            write_file(
                &b.join("litex.config"),
                "[import]\nA = \"../A\"\n\n[export]\nmain = \"./main.lit\"\n",
            );
            write_file(&b.join("main.lit"), "1 = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!ok, "{output}");
            assert!(output.contains("cyclic config import:"), "{output}");
            assert!(output.contains("A") && output.contains("B"), "{output}");
        });
    }

    #[test]
    fn config_imported_child_cannot_use_a_parent_export() {
        run_repository_test_with_large_stack("repository_parent_visibility", || {
            let root = repository_test_dir("root-file-scope");
            let a = root.join("A");
            fs::create_dir_all(&a).expect("create A fixture");
            write_file(
                &root.join("litex.config"),
                "[import]\nA = \"./A\"\n\n[export]\nshared = \"./shared.lit\"\nmain = \"./main.lit\"\n",
            );
            write_file(&root.join("main.lit"), "shared::root_x = 1\n");
            write_file(&root.join("shared.lit"), "have root_x R = 1\n");
            write_project_config(&a, "./main.lit", &[]);
            write_file(&a.join("main.lit"), "shared::root_x = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!ok, "{output}");
            assert!(
                output.contains("shared::root_x")
                    || output.contains("not defined")
                    || output.contains("not authorized"),
                "{output}"
            );
        });
    }

    #[test]
    fn imported_package_grants_dependencies_to_its_exported_subpackages() {
        run_repository_test_with_large_stack("repository_package_capability", || {
            let root = repository_test_dir("package-capability");
            let a = root.join("A");
            let b = a.join("B");
            let x = root.join("X");
            fs::create_dir_all(&b).expect("create subpackage fixture");
            fs::create_dir_all(&x).expect("create dependency fixture");
            write_file(
                &root.join("litex.config"),
                "[import]\nA = \"./A\"\n\n[export]\nmain = \"./main.lit\"\n",
            );
            write_file(&root.join("main.lit"), "A::B::main::result = 1\n");
            write_file(
                &a.join("litex.config"),
                "[import]\nX = \"../X\"\n\n[export]\nB = \"./B\"\nmain = \"./main.lit\"\n",
            );
            write_file(&a.join("main.lit"), "A::B::main::result = 1\n");
            write_file(&b.join("litex.config"), "[export]\nmain = \"./main.lit\"\n");
            write_file(&b.join("main.lit"), "have result R = X::main::value\n");
            write_file(&x.join("litex.config"), "[export]\nmain = \"./main.lit\"\n");
            write_file(&x.join("main.lit"), "have value R = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");

            write_file(
                &b.join("litex.config"),
                "[import]\nX = \"../../X\"\n\n[export]\nmain = \"./main.lit\"\n",
            );
            let (forbidden_ok, forbidden_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!forbidden_ok, "{forbidden_output}");
            assert!(
                forbidden_output
                    .contains("only a repository root or an independently imported package"),
                "{forbidden_output}"
            );
        });
    }

    #[test]
    fn explicit_package_mount_is_distinct_from_a_child_export() {
        run_repository_test_with_large_stack("repository-distinct-mounts", || {
            let root = repository_test_dir("distinct-package-mounts");
            let c = root.join("C");
            let d = c.join("D");
            let b = root.join("B");
            let f = b.join("F");
            fs::create_dir_all(&d).expect("create C::D fixture");
            fs::create_dir_all(&f).expect("create B::F fixture");
            write_file(
                &root.join("litex.config"),
                "[import]\nC = \"./C\"\n\n[export]\nmain = \"./main.lit\"\n",
            );
            write_file(
                &c.join("litex.config"),
                "[import]\nB = \"../B\"\n\n[export]\nD = \"./D\"\n",
            );
            write_file(&b.join("litex.config"), "[export]\nF = \"./F\"\n");
            write_file(&f.join("litex.config"), "[export]\nmain = \"./main.lit\"\n");
            write_file(&f.join("main.lit"), "have value R = 1\n");
            write_file(&d.join("litex.config"), "[export]\nmain = \"./main.lit\"\n");
            write_file(
                &d.join("main.lit"),
                "have from_b R = B::F::main::value\nhave from_bf R = BF::main::value\n",
            );
            write_file(
                &root.join("main.lit"),
                "C::D::main::from_b = 1\nC::D::main::from_bf = 1\n",
            );

            let (undeclared_ok, undeclared_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!undeclared_ok, "{undeclared_output}");
            assert!(undeclared_output.contains("BF"), "{undeclared_output}");

            write_file(
                &c.join("litex.config"),
                "[import]\nB = \"../B\"\nBF = \"../B/F\"\n\n[export]\nD = \"./D\"\n",
            );
            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
            assert!(output.contains("B::F::main::value"), "{output}");
            assert!(output.contains("BF::main::value"), "{output}");
        });
    }

    #[test]
    fn same_named_package_import_is_shared_across_package_boundaries() {
        run_repository_test_with_large_stack("repository-shared-package-import", || {
            let root = repository_test_dir("shared-package-import");
            let b = root.join("B");
            let c = root.join("C");
            let d = c.join("D");
            fs::create_dir_all(&b).expect("create B fixture");
            fs::create_dir_all(&d).expect("create C::D fixture");
            write_file(
                &root.join("litex.config"),
                "[import]\nC = \"./C\"\n\n[export]\nmain = \"./main.lit\"\n",
            );
            write_file(&b.join("litex.config"), "[export]\nmain = \"./main.lit\"\n");
            write_file(&b.join("main.lit"), "have value R = 1\n");
            write_file(
                &c.join("litex.config"),
                "[import]\nB = \"../B\"\n\n[export]\nD = \"./D\"\n",
            );
            write_file(&d.join("litex.config"), "[export]\nmain = \"./main.lit\"\n");
            write_file(&d.join("main.lit"), "have result R = B::main::value\n");
            write_file(
                &root.join("main.lit"),
                "C::D::main::result = 1\nB::main::value = 1\n",
            );

            let (missing_ok, missing_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!missing_ok, "{missing_output}");
            assert!(
                missing_output.contains("project dependency `B::main` is not authorized"),
                "{missing_output}"
            );

            write_file(
                &root.join("litex.config"),
                "[import]\nC = \"./C\"\nB = \"./B\"\n\n[export]\nmain = \"./main.lit\"\n",
            );

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
            assert_eq!(output.matches("have value R = 1").count(), 1, "{output}");
        });
    }

    #[test]
    fn module_flatten_exposes_a_single_file_at_the_module_root() {
        run_repository_test_with_large_stack("repository-module-flatten", || {
            let root = repository_test_dir("module-flatten");
            let y = root.join("Y");
            fs::create_dir_all(&y).expect("create flattened module fixture");
            write_file(
                &root.join("litex.config"),
                "[export]\nY = \"./Y\"\nmain = \"./main.lit\"\n\n[requires]\nmain = [\"Y\"]\n",
            );
            write_file(
                &y.join("litex.config"),
                "[module]\nflatten = true\n\n[export]\nX = \"./implementation.lit\"\n",
            );
            write_file(&y.join("implementation.lit"), "have value R = 1\n");
            write_file(&root.join("main.lit"), "Y::value = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
            assert!(output.contains("Y::value = 1"), "{output}");

            let (file_ok, file_output) = run_source_code_in_file_with_ok(
                y.join("implementation.lit")
                    .to_str()
                    .expect("implementation path is UTF-8"),
            );
            assert!(file_ok, "{file_output}");
            assert!(file_output.contains("have value R = 1"), "{file_output}");

            write_file(&root.join("main.lit"), "Y::X::value = 1\n");
            let (legacy_ok, legacy_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!legacy_ok, "{legacy_output}");
            assert!(legacy_output.contains("Y::X::value"), "{legacy_output}");

            write_file(
                &y.join("litex.config"),
                "[module]\nflatten = false\n\n[export]\nX = \"./implementation.lit\"\n",
            );
            let (unflattened_ok, unflattened_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(unflattened_ok, "{unflattened_output}");
        });
    }

    #[test]
    fn imported_module_flatten_exposes_its_single_file_at_the_package_root() {
        run_repository_test_with_large_stack("repository-imported-module-flatten", || {
            let root = repository_test_dir("imported-module-flatten");
            let b = root.join("B");
            fs::create_dir_all(&b).expect("create imported flattened module fixture");
            write_file(
                &root.join("litex.config"),
                "[import]\nB = \"./B\"\n\n[export]\nmain = \"./main.lit\"\n",
            );
            write_file(
                &b.join("litex.config"),
                "[module]\nflatten = true\n\n[export]\nimplementation = \"./implementation.lit\"\n",
            );
            write_file(&b.join("implementation.lit"), "have value R = 1\n");
            write_file(&root.join("main.lit"), "B::value = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
            assert!(output.contains("B::value = 1"), "{output}");
        });
    }

    #[test]
    fn module_flatten_requires_a_named_single_file_module() {
        run_repository_test_with_large_stack("repository-module-flatten-errors", || {
            let root = repository_test_dir("module-flatten-errors");
            let child = root.join("Child");
            let nested = child.join("Nested");
            fs::create_dir_all(&nested).expect("create flattened module error fixture");

            write_file(
                &root.join("litex.config"),
                "[module]\nflatten = true\n\n[export]\nX = \"./implementation.lit\"\n",
            );
            write_file(&root.join("implementation.lit"), "have value R = 1\n");
            let (root_ok, root_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!root_ok, "{root_output}");
            assert!(
                root_output.contains("requires a named module"),
                "{root_output}"
            );

            write_file(
                &root.join("litex.config"),
                "[export]\nChild = \"./Child\"\n",
            );
            write_file(
                &child.join("litex.config"),
                "[module]\nflatten = true\n\n[export]\nNested = \"./Nested\"\n",
            );
            write_file(
                &nested.join("litex.config"),
                "[export]\nimplementation = \"./implementation.lit\"\n",
            );
            write_file(&nested.join("implementation.lit"), "have value R = 1\n");
            let (directory_ok, directory_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!directory_ok, "{directory_output}");
            assert!(
                directory_output
                    .contains("requires its only [export] entry to point directly to a .lit file"),
                "{directory_output}"
            );
        });
    }

    #[test]
    fn unregistered_files_run_in_isolation() {
        run_repository_test_with_large_stack("file_mode_isolation", || {
            let root = repository_test_dir("file-mode");
            fs::create_dir_all(&root).expect("create repository fixture");
            let config = root.join("litex.config");
            let scratch = root.join("scratch.lit");
            write_project_config(&root, "./main.lit", &[]);
            write_file(&root.join("main.lit"), "1 = 1\n");
            write_file(&scratch, "1 = 1\n");

            let (config_ok, config_output) =
                run_source_code_in_file_with_ok(config.to_str().expect("fixture path is UTF-8"));
            assert!(!config_ok, "{config_output}");
            assert!(
                config_output.contains("litex.config is project configuration"),
                "{config_output}"
            );

            let (scratch_ok, scratch_output) =
                run_source_code_in_file_with_ok(scratch.to_str().expect("fixture path is UTF-8"));
            assert!(scratch_ok, "{scratch_output}");
        });
    }

    #[test]
    fn mod_lit_runs_when_explicitly_configured() {
        run_repository_test_with_large_stack("configured_mod_lit", || {
            let root = repository_test_dir("configured-mod-lit");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_project_config(&root, "./mod.lit", &[]);
            write_file(&root.join("mod.lit"), "1 = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
        });
    }

    #[test]
    fn registered_file_runs_only_its_declared_requirements() {
        run_repository_test_with_large_stack("repository_file_requirements", || {
            let root = repository_test_dir("file-target");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_file(
                &root.join("litex.config"),
                "[export]\nchap6 = \"./chap6.lit\"\nchap7 = \"./chap7.lit\"\npython_chapter = \"./python_chapter.lit\"\nbroken = \"./broken.lit\"\nbook = \"./book.lit\"\n\n[requires]\nchap7 = [\"chap6\"]\n",
            );
            write_file(&root.join("book.lit"), "have title R = 1\n");
            write_file(&root.join("chap6.lit"), "have base R = 1\n");
            write_file(&root.join("chap7.lit"), "have result R = chap6::base\n");
            write_file(&root.join("python_chapter.lit"), "have answer R = 1\n");
            write_file(&root.join("broken.lit"), "1 = 0\n");

            let (entry_ok, entry_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!entry_ok, "{entry_output}");
            assert!(entry_output.contains("1 = 0"), "{entry_output}");

            let (chapter_ok, chapter_output) = run_source_code_in_file_with_ok(
                root.join("chap7.lit")
                    .to_str()
                    .expect("fixture path is UTF-8"),
            );
            assert!(chapter_ok, "{chapter_output}");
            assert!(
                chapter_output.contains("have base R = 1"),
                "{chapter_output}"
            );
            assert!(
                chapter_output.contains("result R = chap6::base"),
                "{chapter_output}"
            );

            let python_output = crate::to_python::to_python_from_file(
                root.join("python_chapter.lit")
                    .to_str()
                    .expect("fixture path is UTF-8"),
            )
            .unwrap_or_else(|error| panic!("project chapter Python failed: {error:?}"));
            assert_eq!(python_output, "answer = 1.0");
        });
    }

    #[test]
    fn file_target_reports_an_undeclared_project_dependency_as_unknown() {
        run_repository_test_with_large_stack("repository_unknown_requirement", || {
            let root = repository_test_dir("unknown-requirement");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_file(
                &root.join("litex.config"),
                "[export]\nchap3 = \"./chap3.lit\"\nchap5 = \"./chap5.lit\"\nchap7 = \"./chap7.lit\"\nmain = \"./main.lit\"\n\n[requires]\nchap7 = [\"chap3\"]\n",
            );
            write_file(&root.join("chap3.lit"), "have value R = 3\n");
            write_file(&root.join("chap5.lit"), "have value R = 5\n");
            write_file(&root.join("chap7.lit"), "have result R = chap3::value\n");
            write_file(&root.join("main.lit"), "chap7::result = 3\n");

            let (ok, output) = run_source_code_in_file_with_ok(
                root.join("chap7.lit")
                    .to_str()
                    .expect("chapter path is UTF-8"),
            );
            assert!(ok, "{output}");
            assert!(!output.contains("value R = 5"), "{output}");

            write_file(&root.join("chap7.lit"), "have result R = chap5::value\n");
            let (missing_ok, missing_output) = run_source_code_in_file_with_ok(
                root.join("chap7.lit")
                    .to_str()
                    .expect("chapter path is UTF-8"),
            );
            assert!(!missing_ok, "{missing_output}");
            assert!(
                missing_output.contains("unknown project dependency `chap5`"),
                "{missing_output}"
            );
        });
    }

    #[test]
    fn trusted_project_exports_skip_checks_but_strict_mode_verifies_them() {
        run_repository_test_with_large_stack("trust_project_export", || {
            let root = repository_test_dir("trust-local-import");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_ordered_project_config(
                &root,
                &[
                    ("chap10", "./chap10.lit", true),
                    ("book", "./book.lit", false),
                ],
            );
            write_file(&root.join("chap10.lit"), "have bad N = -1\n");
            write_file(&root.join("book.lit"), "chap10::bad = -1\n");
            let (ordinary_ok, ordinary_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                true,
            );
            assert!(ordinary_ok, "{ordinary_output}");
            assert!(
                ordinary_output.contains("\"trust_dependencies\"")
                    && ordinary_output.contains("\"trust_project_export\": 1"),
                "{ordinary_output}"
            );

            let (strict_ok, strict_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                true,
                OutputLanguage::English,
                false,
            );
            assert!(!strict_ok, "{strict_output}");
            assert!(
                !strict_output.contains("trust_project_export"),
                "{strict_output}"
            );
        });
    }

    #[test]
    fn strict_mode_ignores_project_trust_for_a_valid_prefix() {
        run_repository_test_with_large_stack("strict-project-export", || {
            let root = repository_test_dir("strict-run-plan-cache");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_file(
                &root.join("litex.config"),
                "[export]\nchap1 = \"./chap1.lit\"\ntrust chap2 = \"./chap2.lit\"\n\n[requires]\nchap2 = [\"chap1\"]\n",
            );
            write_file(&root.join("chap1.lit"), "have x R = 1\n");
            write_file(&root.join("chap2.lit"), "chap1::x = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                true,
                OutputLanguage::English,
                true,
            );
            assert!(ok, "{output}");
            assert!(!output.contains("\"trust_project_export\": 1"), "{output}");

            let chapter_output = run_source_code_in_file_for_cli_with_strict(
                root.join("chap2.lit")
                    .to_str()
                    .expect("fixture path is UTF-8"),
                true,
                true,
            );
            assert!(!chapter_output.contains("\"error\""), "{chapter_output}");
        });
    }

    #[test]
    fn run_plan_executes_child_repositories_in_order_and_reuses_them() {
        run_repository_test_with_large_stack("run-plan-child-repository", || {
            let root = repository_test_dir("run-plan-child-repository");
            let child = root.join("A");
            fs::create_dir_all(&child).expect("create repository fixture");
            write_file(
                &root.join("litex.config"),
                "[import]\nA = \"./A\"\n\n[export]\nbefore = \"./before.lit\"\nafter = \"./after.lit\"\nmain = \"./main.lit\"\n",
            );
            write_ordered_project_config(&child, &[("main", "./main.lit", false)]);
            write_file(&root.join("before.lit"), "have before R = 1\n");
            write_file(&child.join("main.lit"), "have inner R = 1\n");
            write_file(
                &root.join("after.lit"),
                "A::main::inner = 1\nhave after R = 1\n",
            );
            write_file(&root.join("main.lit"), "1 = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
            let before = output.find("have before R = 1").expect("before output");
            let inner = output.find("have inner R = 1").expect("child output");
            let after = output.find("have after R = 1").expect("after output");
            assert!(inner < before && before < after, "{output}");
            assert_eq!(output.matches("have inner R = 1").count(), 1, "{output}");
        });
    }

    #[test]
    fn ordered_plan_rejects_a_later_canonical_reference_during_execution() {
        run_repository_test_with_large_stack("run-plan-later-dependency", || {
            let root = repository_test_dir("run-plan-later-dependency");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_ordered_project_config(
                &root,
                &[
                    ("chap1", "./chap1.lit", false),
                    ("chap2", "./chap2.lit", false),
                ],
            );
            write_file(&root.join("chap1.lit"), "chap2::x = 1\n");
            write_file(&root.join("chap2.lit"), "have x R = 1\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!ok, "{output}");
            assert!(
                output.contains("identifier `chap2::x` not defined"),
                "{output}"
            );
        });
    }

    #[test]
    fn project_module_tuple_definitions_and_proof_bindings_keep_their_scope() {
        run_repository_test_with_large_stack("project_module_tuple_scope", || {
            let root = repository_test_dir("project-module-tuple-scope");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_project_config(&root, "./book.lit", &[("chapter", "./chapter.lit")]);
            write_file(
                &root.join("chapter.lit"),
                r#"
have n N_pos = 3
have tuple index_tuple for i <= n, index_tuple[i] = i

prop has_self_witness(x R):
    exist y R st {y = x}

thm self_witness_can_be_obtained:
    ? forall x R:
        $has_self_witness(x)
        =>:
            x = x
    obtain y from exist y R st {y = x}
    y = x
    x = y = x
"#,
            );
            write_file(&root.join("book.lit"), "chapter::n = 3\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(ok, "{output}");
        });
    }

    #[test]
    fn trusted_config_import_is_transitive_and_strict_mode_verifies_it() {
        run_repository_test_with_large_stack("trusted_config_import", || {
            let root = repository_test_dir("trust-import");
            let a = root.join("A");
            fs::create_dir_all(&a).expect("create repository fixture");
            write_file(
                &root.join("litex.config"),
                "[import]\ntrust A = \"./A\"\n\n[export]\nbook = \"./book.lit\"\n",
            );
            write_project_config(&a, "./main.lit", &[("chap10", "./chap10.lit")]);
            write_file(&a.join("main.lit"), "1 = 1\n");
            write_file(
                &a.join("chap10.lit"),
                "abstract_prop trusted_prop(x)\n\nthm trusted_all:\n    ? forall x R:\n        =>:\n            $trusted_prop(x)\n",
            );

            write_file(
                &root.join("book.lit"),
                "by thm A::chap10::trusted_all(2)\n$A::chap10::trusted_prop(2)\n",
            );
            let (trusted_ok, trusted_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(trusted_ok, "{trusted_output}");

            let (strict_ok, strict_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                true,
                OutputLanguage::English,
                false,
            );
            assert!(!strict_ok, "{strict_output}");
            assert!(
                !strict_output.contains("trust_project_import"),
                "{strict_output}"
            );

            let mut runtime = Runtime::new();
            discover_repository(&mut runtime, root.to_str().expect("fixture path is UTF-8"))
                .expect("discover trusted fixture");
            let entry = runtime.current_module_id();
            let (results, error) = crate::pipeline::run_repository_file_target(
                &mut runtime,
                RepositoryFileTarget::Module(entry),
            );
            assert!(error.is_none(), "trusted config fixture should run");
            let trust_summary = runtime.proof_trust_summary_from_stmt_results(&results);
            assert!(
                trust_summary
                    .dependencies
                    .iter()
                    .any(|dependency| dependency.kind == "trust_project_import"),
                "trusted config import must taint the run summary"
            );
        });
    }

    #[test]
    fn config_standard_import_selects_a_generic_std_child_module() {
        run_repository_test_with_large_stack("config_standard_import", || {
            let root = repository_test_dir("config-standard-import");
            let std_root = root.join("installed-std");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_standard_library_fixture(&std_root);
            write_file(
                &root.join("litex.config"),
                "[import std]\nbasics\n\n[export]\nmain = \"./main.lit\"\n",
            );
            write_file(&root.join("main.lit"), "std::basics::value = 1\n");

            with_standard_library_root(&std_root, || {
                let mut runtime = Runtime::new();
                discover_repository(&mut runtime, root.to_str().expect("fixture path is UTF-8"))
                    .expect("discover standard import fixture");
                let std_module_id = runtime
                    .module_manager
                    .module_id_by_name("std")
                    .expect("standard root should be a generic module");
                assert!(runtime
                    .module_manager
                    .module_id_by_name("std::basics")
                    .is_some());
                assert!(runtime.module_manager.module_id_by_name("basics").is_none());
                let std_module = runtime
                    .module_manager
                    .module(std_module_id)
                    .expect("standard root should be registered");
                assert!(std_module.exports.contains_key("basics"));
                assert!(!std_module.exports.contains_key("other"));
                let entry_module = runtime.current_module_id();
                assert!(runtime
                    .module_manager
                    .module(entry_module)
                    .expect("entry module should exist")
                    .config_imports
                    .iter()
                    .any(|import| import.module_id == std_module_id));

                let (results, runtime_error) = crate::pipeline::run_repository_file_target(
                    &mut runtime,
                    RepositoryFileTarget::Module(entry_module),
                );
                assert!(runtime_error.is_none(), "{runtime_error:?}");
                assert!(!results.is_empty(), "standard package should execute");
                assert!(runtime
                    .module_manager
                    .module_id_by_name("std::unused")
                    .is_none());
            });
        });
    }

    #[test]
    fn source_standard_import_selects_new_children_after_the_std_root_is_loaded() {
        run_repository_test_with_large_stack("source_standard_import", || {
            let root = repository_test_dir("source-standard-import");
            let std_root = root.join("installed-std");
            fs::create_dir_all(&root).expect("create source fixture");
            write_standard_library_fixture(&std_root);

            with_standard_library_root(&std_root, || {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope("source-standard-import.lit");
                let (results, runtime_error) = crate::pipeline::run_source_code(
                    "import std basics\nstd::basics::value = 1\nimport std other\nstd::other::value = 1\n",
                    &mut runtime,
                );
                assert!(runtime_error.is_none(), "{runtime_error:?}");
                assert!(runtime.module_manager.module_id_by_name("std").is_some());
                assert!(runtime
                    .module_manager
                    .module_id_by_name("std::basics")
                    .is_some());
                assert!(runtime
                    .module_manager
                    .module_id_by_name("std::other")
                    .is_some());
                assert!(runtime.module_manager.module_id_by_name("basics").is_none());
                let trust_summary = runtime.proof_trust_summary_from_stmt_results(&results);
                assert!(
                    !trust_summary
                        .dependencies
                        .iter()
                        .any(|dependency| dependency.kind == "std_package"),
                    "standard imports use ordinary module execution, not a trust marker"
                );
            });
        });
    }

    #[test]
    fn later_standard_import_runs_the_selected_root_requirements() {
        run_repository_test_with_large_stack("source_standard_import_requirements", || {
            let root = repository_test_dir("source-standard-import-requirements");
            let std_root = root.join("installed-std");
            fs::create_dir_all(&root).expect("create source fixture");
            write_standard_library_fixture(&std_root);

            with_standard_library_root(&std_root, || {
                let mut runtime = Runtime::new();
                runtime.new_file_path_new_env_new_name_scope(
                    "source-standard-import-requirements.lit",
                );
                let (_, runtime_error) = crate::pipeline::run_source_code(
                    "import std seed\nstd::seed::value = 0\nimport std other\nstd::other::value = 1\n",
                    &mut runtime,
                );
                assert!(runtime_error.is_none(), "{runtime_error:?}");
            });
        });
    }

    #[test]
    fn standard_library_root_candidates_cover_installed_layouts() {
        let deb_executable = PathBuf::from("/opt/litex/usr/local/bin/litex");
        let deb_roots = standard_library_root_candidates(None, None, Some(deb_executable));
        assert!(deb_roots.contains(&PathBuf::from(
            "/opt/litex/usr/local/bin/../../share/litex/std"
        )));

        let sibling_executable = PathBuf::from("/opt/litex/bin/litex");
        let sibling_roots = standard_library_root_candidates(None, None, Some(sibling_executable));
        assert!(sibling_roots.contains(&PathBuf::from("/opt/litex/bin/../std")));
    }

    fn run_repository_test_with_large_stack(name: &str, test: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name(name.to_string())
            .stack_size(LARGE_REPOSITORY_TEST_STACK_SIZE)
            .spawn(test)
            .expect("spawn repository test")
            .join()
            .unwrap();
    }

    fn repository_test_dir(name: &str) -> PathBuf {
        std::env::temp_dir().join(format!("litex-repository-{}-{}", name, std::process::id()))
    }

    fn write_file(path: &Path, content: &str) {
        fs::write(path, content).expect("write repository fixture");
    }

    fn write_project_config(root: &Path, run_file: &str, exports: &[(&str, &str)]) {
        let mut entries = exports
            .iter()
            .map(|(name, path)| (*name, *path, false))
            .collect::<Vec<_>>();
        if !entries.iter().any(|(_, path, _)| *path == run_file) {
            entries.push(("main", run_file, false));
        }
        write_ordered_project_config(root, entries.as_slice());
    }

    fn write_ordered_project_config(root: &Path, entries: &[(&str, &str, bool)]) {
        let mut content = String::from("[export]\n");
        for (name, path, trusted) in entries {
            let prefix = if *trusted { "trust " } else { "" };
            content.push_str(format!("{}{} = \"{}\"\n", prefix, name, path).as_str());
        }
        write_file(&root.join("litex.config"), content.as_str());
    }

    fn write_standard_library_fixture(std_root: &Path) {
        let basics = std_root.join("basics");
        let seed = std_root.join("seed");
        let other = std_root.join("other");
        let unused = std_root.join("unused");
        let support = std_root.join("support");
        fs::create_dir_all(&basics).expect("create basics fixture");
        fs::create_dir_all(&seed).expect("create seed fixture");
        fs::create_dir_all(&other).expect("create other fixture");
        fs::create_dir_all(&unused).expect("create unused fixture");
        fs::create_dir_all(&support).expect("create support fixture");
        write_file(
            &std_root.join("litex.config"),
            "[import]\nsupport = \"./support\"\n\n[export]\nseed = \"./seed\"\nbasics = \"./basics\"\nother = \"./other\"\nunused = \"./unused\"\n\n[requires]\nother = [\"basics\"]\n",
        );
        write_file(
            &support.join("litex.config"),
            "[module]\nflatten = true\n\n[export]\nimplementation = \"./main.lit\"\n",
        );
        write_file(&support.join("main.lit"), "have value R = 1\n");
        write_file(
            &basics.join("litex.config"),
            "[module]\nflatten = true\n\n[export]\nimplementation = \"./main.lit\"\n",
        );
        write_file(&basics.join("main.lit"), "have value R = support::value\n");
        write_file(
            &seed.join("litex.config"),
            "[module]\nflatten = true\n\n[export]\nimplementation = \"./main.lit\"\n",
        );
        write_file(&seed.join("main.lit"), "have value R = 0\n");
        write_file(
            &other.join("litex.config"),
            "[module]\nflatten = true\n\n[export]\nimplementation = \"./main.lit\"\n",
        );
        write_file(
            &other.join("main.lit"),
            "have value R = std::basics::value\n",
        );
        write_file(
            &unused.join("litex.config"),
            "[module]\nflatten = true\n\n[export]\nimplementation = \"./main.lit\"\n",
        );
        write_file(&unused.join("main.lit"), "1 = 0\n");
    }

    fn with_standard_library_root(std_root: &Path, test: impl FnOnce()) {
        let lock = standard_library_root_env_lock()
            .lock()
            .expect("lock standard library root environment");
        let _restore = StandardLibraryRootEnvGuard::new();
        std::env::set_var("LITEX_STD_PATH", std_root);
        test();
        drop(lock);
    }

    fn standard_library_root_env_lock() -> &'static std::sync::Mutex<()> {
        static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
        LOCK.get_or_init(|| std::sync::Mutex::new(()))
    }

    struct StandardLibraryRootEnvGuard {
        previous: Option<std::ffi::OsString>,
    }

    impl StandardLibraryRootEnvGuard {
        fn new() -> Self {
            StandardLibraryRootEnvGuard {
                previous: std::env::var_os("LITEX_STD_PATH"),
            }
        }
    }

    impl Drop for StandardLibraryRootEnvGuard {
        fn drop(&mut self) {
            if let Some(previous) = self.previous.as_ref() {
                std::env::set_var("LITEX_STD_PATH", previous);
            } else {
                std::env::remove_var("LITEX_STD_PATH");
            }
        }
    }
}
