use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

const LITEX_CONFIG: &str = "litex.config";
const LEGACY_MOD_DOT_LIT: &str = "mod.lit";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FileNode {
    module_id: ModuleId,
    file_id: FileId,
}

#[derive(Clone, Copy)]
pub enum RepositoryFileTarget {
    Entrance(ModuleId),
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
    let main_lit_path = resolve_entrance_file(&repository_root, &config, &config_path)?;

    let repository_root_string = path_string(&repository_root, repository_path, 0)?;
    let main_lit_string = path_string(&main_lit_path, repository_path, 0)?;
    let root_module_id = runtime
        .new_repository_path_new_env_new_name_scope(repository_root_string, main_lit_string.clone())
        .map_err(|message| repository_error(message, repository_path, 0))?;

    discover_module_config(runtime, root_module_id, &config_path, config)?;
    let module_import_edges = scan_repository_dependencies(runtime)?;
    reject_cyclic_local_imports(runtime)?;
    reject_cyclic_module_imports(runtime, &module_import_edges)?;
    Ok(main_lit_string)
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
        if repository_target_for_path(&probe, canonical_file_string.as_str()).is_none() {
            continue;
        }
        discover_repository(runtime, root_string.as_str())?;
        return Ok(repository_target_for_path(
            runtime,
            canonical_file_string.as_str(),
        ));
    }
    Ok(None)
}

fn repository_target_for_path(
    runtime: &Runtime,
    source_path: &str,
) -> Option<RepositoryFileTarget> {
    for module in runtime.module_manager.modules.values() {
        if module.main_file_path == source_path {
            return Some(RepositoryFileTarget::Entrance(module.id));
        }
        for file in module.files.iter() {
            if file.source_path == source_path {
                return Some(RepositoryFileTarget::File {
                    module_id: module.id,
                    file_id: file.id,
                });
            }
        }
    }
    None
}

fn discover_module_config(
    runtime: &mut Runtime,
    module_id: ModuleId,
    config_path: &Path,
    config: ProjectConfig,
) -> Result<(), RuntimeError> {
    for export in config.exports {
        discover_config_export(runtime, module_id, config_path, export)?;
    }
    Ok(())
}

fn discover_config_export(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    config_path: &Path,
    export: ProjectExport,
) -> Result<(), RuntimeError> {
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
        if canonical_path.file_name().and_then(|name| name.to_str()) == Some(LEGACY_MOD_DOT_LIT) {
            return Err(repository_error(
                "mod.lit is obsolete; migrate declarations to litex.config".to_string(),
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
            .register_exported_file(canonical_name, source_path, target)
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
        if is_root {
            runtime
                .module_manager
                .register_root_export(export.name, target)
                .map_err(|message| {
                    repository_error(message, &config_path.to_string_lossy(), export.line)
                })?;
        }
    } else if target_path.is_dir() {
        let canonical_root = canonical_directory(
            &target_path.to_string_lossy(),
            &config_path.to_string_lossy(),
            export.line,
        )?;
        let child_config_path =
            require_project_config(&canonical_root, &config_path.to_string_lossy(), export.line)?;
        let child_config = read_project_config(&child_config_path)?;
        let child_main_lit =
            resolve_entrance_file(&canonical_root, &child_config, &child_config_path)?;
        let child_name = join_module_name(&owner_name, &export.name);
        let child_root_string =
            path_string(&canonical_root, &config_path.to_string_lossy(), export.line)?;
        let child_main_string =
            path_string(&child_main_lit, &config_path.to_string_lossy(), export.line)?;
        let child_module_id = runtime
            .module_manager
            .create_discovered_module(child_name, child_root_string, child_main_string)
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
        discover_module_config(runtime, child_module_id, &child_config_path, child_config)?;
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
    Ok(())
}

fn scan_repository_dependencies(
    runtime: &mut Runtime,
) -> Result<HashMap<ModuleId, Vec<ModuleId>>, RuntimeError> {
    let mut module_import_edges = HashMap::new();
    let module_ids = runtime
        .module_manager
        .modules
        .keys()
        .copied()
        .collect::<Vec<ModuleId>>();
    for module_id in module_ids {
        let (main_path, exported_files) = {
            let module = runtime
                .module_manager
                .module(module_id)
                .expect("discovered module should exist");
            let files = module
                .files
                .iter()
                .map(|file| (file.id, file.source_path.clone()))
                .collect::<Vec<(FileId, String)>>();
            (module.main_file_path.clone(), files)
        };

        let (main_imports, main_module_imports) =
            scan_source_dependencies(runtime, module_id, &main_path)?;
        let main_edges = module_import_edges
            .entry(module_id)
            .or_insert_with(Vec::new);
        for imported_module in main_module_imports {
            if !main_edges.contains(&imported_module) {
                main_edges.push(imported_module);
            }
        }
        runtime
            .module_manager
            .module_mut(module_id)
            .expect("discovered module should exist")
            .main_local_imports = main_imports;

        for (file_id, source_path) in exported_files {
            let (imports, imported_modules) =
                scan_source_dependencies(runtime, module_id, &source_path)?;
            let edges = module_import_edges
                .entry(module_id)
                .or_insert_with(Vec::new);
            for imported_module in imported_modules {
                if !edges.contains(&imported_module) {
                    edges.push(imported_module);
                }
            }
            runtime
                .module_manager
                .module_mut(module_id)
                .and_then(|module| module.file_mut(file_id))
                .expect("exported file should exist")
                .local_imports = imports;
        }
    }
    Ok(module_import_edges)
}

fn scan_source_dependencies(
    runtime: &Runtime,
    owner_module_id: ModuleId,
    source_path: &str,
) -> Result<(HashMap<String, ImportTarget>, Vec<ModuleId>), RuntimeError> {
    let content = fs::read_to_string(source_path).map_err(|error| {
        repository_error(
            format!("failed to read module source `{}`: {}", source_path, error),
            source_path,
            0,
        )
    })?;
    let mut tokenizer = Tokenizer::new();
    let blocks = tokenizer.parse_blocks(&content, Rc::from(source_path))?;
    let mut imports = HashMap::new();
    let mut module_imports = vec![];
    for mut block in blocks {
        reject_nested_local_imports(&block.body)?;
        let first_token = block.header.first().map(String::as_str);
        if first_token == Some(EXPORT) {
            return Err(repository_error(
                "`export` is configured in litex.config and is not a Litex statement".to_string(),
                source_path,
                block.line_file.0,
            ));
        }
        let is_trust_import =
            first_token == Some(TRUST) && block.header.get(1).map(String::as_str) == Some(IMPORT);
        if first_token == Some(IMPORT) || is_trust_import {
            let statement = if is_trust_import {
                runtime.parse_trust_stmt(&mut block)?
            } else {
                runtime.parse_import_stmt(&mut block)?
            };
            let import = match statement {
                Stmt::Command(CommandStmt::ImportStmt(import)) => import,
                Stmt::Command(CommandStmt::TrustImportStmt(trust_import)) => trust_import.import,
                _ => unreachable!("import parser should produce an import statement"),
            };
            match import {
                ImportStmt::ImportRelativePath(_) => {
                    return Err(repository_error(
                        "project mode import must name a root export or globally registered module; use litex.config and local_import for module-local dependencies"
                            .to_string(),
                        source_path,
                        block.line_file.0,
                    ));
                }
                ImportStmt::ImportGlobalModule(global_import) => {
                    if let Some(target) =
                        runtime.module_manager.root_export(&global_import.mod_name)
                    {
                        let ImportTarget::Module(imported_module_id) = target else {
                            return Err(repository_error(
                                format!(
                                    "root export `{}` is a file; files can only be loaded with local_import inside their owner module",
                                    global_import.mod_name
                                ),
                                source_path,
                                block.line_file.0,
                            ));
                        };
                        if !module_imports.contains(&imported_module_id) {
                            module_imports.push(imported_module_id);
                        }
                    }
                }
            }
            continue;
        }
        let is_trust_local_import = first_token == Some(TRUST)
            && block.header.get(1).map(String::as_str) == Some(LOCAL_IMPORT);
        if first_token != Some(LOCAL_IMPORT) && !is_trust_local_import {
            continue;
        }
        if !block.body.is_empty() {
            return Err(repository_error(
                "local_import and trust local_import cannot have a body".to_string(),
                source_path,
                block.line_file.0,
            ));
        }
        let statement = if is_trust_local_import {
            runtime.parse_trust_stmt(&mut block)?
        } else {
            runtime.parse_local_import_stmt(&mut block)?
        };
        let local_import = match statement {
            Stmt::Command(CommandStmt::LocalImportStmt(local_import)) => local_import,
            Stmt::Command(CommandStmt::TrustLocalImportStmt(trust_local_import)) => {
                trust_local_import.local_import
            }
            _ => unreachable!("local import parser should produce a local import statement"),
        };
        let target = runtime
            .module_manager
            .module(owner_module_id)
            .and_then(|module| module.exports.get(&local_import.name))
            .map(|entry| entry.target(owner_module_id))
            .ok_or_else(|| {
                repository_error(
                    format!(
                        "local_import `{}` is not declared by this module's litex.config",
                        local_import.name
                    ),
                    source_path,
                    local_import.line_file.0,
                )
            })?;
        if let ImportTarget::Module(imported_module_id) = target {
            if !module_imports.contains(&imported_module_id) {
                module_imports.push(imported_module_id);
            }
        }
        if imports.insert(local_import.name.clone(), target).is_some() {
            return Err(repository_error(
                format!("duplicate local_import `{}`", local_import.name),
                source_path,
                local_import.line_file.0,
            ));
        }
    }
    Ok((imports, module_imports))
}

fn reject_nested_local_imports(blocks: &[TokenBlock]) -> Result<(), RuntimeError> {
    for block in blocks {
        let first_token = block.header.first().map(String::as_str);
        let is_trust_local_import = first_token == Some(TRUST)
            && block.header.get(1).map(String::as_str) == Some(LOCAL_IMPORT);
        if first_token == Some(LOCAL_IMPORT) || is_trust_local_import {
            return Err(repository_error(
                "local_import and trust local_import are only allowed as top-level source statements"
                    .to_string(),
                block.line_file.1.as_ref(),
                block.line_file.0,
            ));
        }
        reject_nested_local_imports(&block.body)?;
    }
    Ok(())
}

fn reject_cyclic_local_imports(runtime: &Runtime) -> Result<(), RuntimeError> {
    let mut edges = HashMap::<FileNode, Vec<FileNode>>::new();
    for module in runtime.module_manager.modules.values() {
        for file in module.files.iter() {
            let node = FileNode {
                module_id: module.id,
                file_id: file.id,
            };
            let dependencies = file
                .local_imports
                .values()
                .filter_map(|target| match target {
                    ImportTarget::File { module_id, file_id } => Some(FileNode {
                        module_id: *module_id,
                        file_id: *file_id,
                    }),
                    ImportTarget::Module(_) => None,
                })
                .collect::<Vec<FileNode>>();
            edges.insert(node, dependencies);
        }
    }

    let mut visited = HashSet::new();
    let mut visiting = HashSet::new();
    let mut stack = vec![];
    for node in edges.keys().copied().collect::<Vec<FileNode>>() {
        if let Some(cycle) =
            find_local_import_cycle(node, &edges, &mut visited, &mut visiting, &mut stack)
        {
            let names = cycle
                .iter()
                .map(|cycle_node| file_node_name(runtime, *cycle_node))
                .collect::<Vec<String>>();
            let source_path = runtime
                .module_manager
                .module(node.module_id)
                .and_then(|module| module.file(node.file_id))
                .map(|file| file.source_path.as_str())
                .unwrap_or("");
            return Err(repository_error(
                format!("cyclic local import: {}", names.join(" -> ")),
                source_path,
                0,
            ));
        }
    }
    Ok(())
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

fn find_local_import_cycle(
    node: FileNode,
    edges: &HashMap<FileNode, Vec<FileNode>>,
    visited: &mut HashSet<FileNode>,
    visiting: &mut HashSet<FileNode>,
    stack: &mut Vec<FileNode>,
) -> Option<Vec<FileNode>> {
    if visited.contains(&node) {
        return None;
    }
    if visiting.contains(&node) {
        let start = stack.iter().position(|item| *item == node).unwrap_or(0);
        let mut cycle = stack[start..].to_vec();
        cycle.push(node);
        return Some(cycle);
    }

    visiting.insert(node);
    stack.push(node);
    if let Some(dependencies) = edges.get(&node) {
        for dependency in dependencies {
            if let Some(cycle) =
                find_local_import_cycle(*dependency, edges, visited, visiting, stack)
            {
                return Some(cycle);
            }
        }
    }
    stack.pop();
    visiting.remove(&node);
    visited.insert(node);
    None
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

fn file_node_name(runtime: &Runtime, node: FileNode) -> String {
    runtime
        .module_manager
        .module(node.module_id)
        .and_then(|module| module.file(node.file_id))
        .map(|file| file.canonical_name.clone())
        .unwrap_or_else(|| format!("file#{}", node.file_id.0))
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
    let legacy_path = directory.join(LEGACY_MOD_DOT_LIT);
    if legacy_path.is_file() {
        return Err(repository_error(
            format!(
                "{} is obsolete; move its declarations to {}/{}",
                legacy_path.to_string_lossy(),
                directory.to_string_lossy(),
                LITEX_CONFIG
            ),
            source_path,
            line,
        ));
    }
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

fn resolve_entrance_file(
    root: &Path,
    config: &ProjectConfig,
    config_path: &Path,
) -> Result<PathBuf, RuntimeError> {
    let path = canonical_file(
        &root.join(&config.entrance_path),
        &config_path.to_string_lossy(),
        config.entrance_line,
    )?;
    if path.extension().and_then(|extension| extension.to_str()) != Some("lit") {
        return Err(repository_error(
            "[entrance].file must point to a .lit file".to_string(),
            &config_path.to_string_lossy(),
            config.entrance_line,
        ));
    }
    if path.file_name().and_then(|name| name.to_str()) == Some(LEGACY_MOD_DOT_LIT) {
        return Err(repository_error(
            "[entrance].file cannot point to obsolete mod.lit".to_string(),
            &config_path.to_string_lossy(),
            config.entrance_line,
        ));
    }
    Ok(path)
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

#[cfg(test)]
mod tests {
    use super::*;

    const LARGE_REPOSITORY_TEST_STACK_SIZE: usize = 64 * 1024 * 1024;

    #[test]
    fn repository_exports_and_local_imports_use_canonical_namespaces() {
        run_repository_test_with_large_stack("repository_exports", || {
            let root = repository_test_dir("exports");
            let a = root.join("A");
            let chapters = a.join("chapters");
            fs::create_dir_all(&chapters).expect("create repository fixture");
            write_project_config(&root, "./main.lit", &[("A", "./A")]);
            write_file(
                &root.join("main.lit"),
                "import A\n\nA::chapters::leaf::x = 1\n",
            );
            write_project_config(
                &a,
                "./main.lit",
                &[
                    ("chap2", "./chap2.lit"),
                    ("chap3", "./chap3.lit"),
                    ("chapters", "./chapters"),
                ],
            );
            write_file(
                &a.join("main.lit"),
                "local_import chap3\nlocal_import chapters\n\nchap3::z = 1\n",
            );
            write_file(&a.join("chap2.lit"), "have x R = 1\n");
            write_file(
                &a.join("chap3.lit"),
                "local_import chap2\n\nhave z R = chap2::x\n",
            );
            write_project_config(&chapters, "./main.lit", &[("leaf", "./leaf.lit")]);
            write_file(
                &chapters.join("main.lit"),
                "local_import leaf\n\nleaf::x = 1\n",
            );
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

            let latex_output =
                crate::to_latex::to_latex_from_repository_after_builtins(repository_path)
                    .unwrap_or_else(|error| panic!("repository LaTeX failed: {error:?}"));
            assert!(latex_output.contains("A::chap3"), "{latex_output}");

            let python_output =
                crate::to_python::to_python_from_repository_after_builtins(repository_path)
                    .unwrap_or_else(|error| panic!("repository Python failed: {error:?}"));
            assert_eq!(python_output, "answer = 1.0");

            let chapter_path = root.join("A").join("chap3.lit");
            let chapter_path_string = chapter_path.to_str().expect("chapter path is UTF-8");
            let (chapter_ok, chapter_output) = run_source_code_in_file_with_ok(chapter_path_string);
            assert!(chapter_ok, "{chapter_output}");
            assert!(chapter_output.contains("A::chap2::x"), "{chapter_output}");

            let (chapter_runner_ok, chapter_runner_output) =
                run_runner_for_file(chapter_path_string, true);
            assert!(chapter_runner_ok, "{chapter_runner_output}");

            let (chapter_graph_ok, chapter_graph_output) =
                run_graph_for_file(chapter_path_string, true);
            assert!(chapter_graph_ok, "{chapter_graph_output}");

            let chapter_latex =
                crate::to_latex::to_latex_from_file_after_builtins(chapter_path_string)
                    .unwrap_or_else(|error| panic!("project chapter LaTeX failed: {error:?}"));
            assert!(
                chapter_latex.contains("local\\_import chap2"),
                "{chapter_latex}"
            );

            let mut isolated_runtime = Runtime::new_with_builtin_code();
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
    fn repository_discovery_rejects_local_import_cycles_before_execution() {
        run_repository_test_with_large_stack("repository_cycle", || {
            let root = repository_test_dir("cycle");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_project_config(&root, "./main.lit", &[("a", "./a.lit"), ("b", "./b.lit")]);
            write_file(&root.join("main.lit"), "local_import a\n");
            write_file(&root.join("a.lit"), "local_import b\n");
            write_file(&root.join("b.lit"), "local_import a\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!ok, "{output}");
            assert!(output.contains("cyclic local import:"), "{output}");
            assert!(
                output.contains("a -> b -> a") || output.contains("b -> a -> b"),
                "{output}"
            );
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
            write_project_config(&root, "./main.lit", &[("A", "./A"), ("B", "./B")]);
            write_file(&root.join("main.lit"), "import A\n");
            write_project_config(&a, "./main.lit", &[]);
            write_file(&a.join("main.lit"), "import B\n");
            write_project_config(&b, "./main.lit", &[]);
            write_file(&b.join("main.lit"), "import A\n");

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!ok, "{output}");
            assert!(output.contains("cyclic module import:"), "{output}");
            assert!(
                output.contains("A -> B -> A") || output.contains("B -> A -> B"),
                "{output}"
            );
            assert!(!output.contains("cyclic local import:"), "{output}");
        });
    }

    #[test]
    fn root_file_export_does_not_leak_into_an_imported_module() {
        run_repository_test_with_large_stack("repository_root_file_scope", || {
            let root = repository_test_dir("root-file-scope");
            let a = root.join("A");
            fs::create_dir_all(&a).expect("create A fixture");
            write_project_config(
                &root,
                "./main.lit",
                &[("shared", "./shared.lit"), ("A", "./A")],
            );
            write_file(
                &root.join("main.lit"),
                "local_import shared\nshared::root_x = 1\nimport A\n",
            );
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
                output.contains("identifier `shared::root_x` not defined"),
                "{output}"
            );
        });
    }

    #[test]
    fn file_mode_rejects_configs_exports_and_unregistered_local_imports() {
        run_repository_test_with_large_stack("file_mode_module_syntax", || {
            let root = repository_test_dir("file-mode");
            fs::create_dir_all(&root).expect("create repository fixture");
            let config = root.join("litex.config");
            let export_script = root.join("export-script.lit");
            let local_import_script = root.join("local-import-script.lit");
            write_project_config(&root, "./main.lit", &[]);
            write_file(&export_script, "export file \"./x.lit\" as x\n");
            write_file(&local_import_script, "local_import x\n");

            let (config_ok, config_output) =
                run_source_code_in_file_with_ok(config.to_str().expect("fixture path is UTF-8"));
            assert!(!config_ok, "{config_output}");
            assert!(
                config_output.contains("litex.config is project configuration"),
                "{config_output}"
            );

            let (export_ok, export_output) = run_source_code_in_file_with_ok(
                export_script.to_str().expect("fixture path is UTF-8"),
            );
            assert!(!export_ok, "{export_output}");
            assert!(
                export_output.contains("`export` is configured in litex.config"),
                "{export_output}"
            );

            let (local_ok, local_output) = run_source_code_in_file_with_ok(
                local_import_script.to_str().expect("fixture path is UTF-8"),
            );
            assert!(!local_ok, "{local_output}");
            assert!(
                local_output.contains("local_import is unavailable in isolated file mode"),
                "{local_output}"
            );
        });
    }

    #[test]
    fn repository_mode_rejects_legacy_mod_lit_with_migration_message() {
        run_repository_test_with_large_stack("legacy_mod_lit", || {
            let root = repository_test_dir("legacy-mod-lit");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_file(
                &root.join("mod.lit"),
                "export file \"./chap1.lit\" as chap1\n",
            );

            let (ok, output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!ok, "{output}");
            assert!(output.contains("mod.lit is obsolete"), "{output}");
            assert!(output.contains("litex.config"), "{output}");
        });
    }

    #[test]
    fn registered_file_runs_its_local_import_closure_without_running_unrelated_exports() {
        run_repository_test_with_large_stack("repository_file_target", || {
            let root = repository_test_dir("file-target");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_project_config(
                &root,
                "./book.lit",
                &[
                    ("chap6", "./chap6.lit"),
                    ("chap7", "./chap7.lit"),
                    ("python_chapter", "./python_chapter.lit"),
                    ("broken", "./broken.lit"),
                ],
            );
            write_file(&root.join("book.lit"), "have title R = 1\n");
            write_file(&root.join("chap6.lit"), "have base R = 1\n");
            write_file(
                &root.join("chap7.lit"),
                "local_import chap6\n\nhave result R = chap6::base\n",
            );
            write_file(
                &root.join("python_chapter.lit"),
                "local_import chap6\n\nhave answer R = 1\n",
            );
            write_file(&root.join("broken.lit"), "1 = 0\n");

            let (entry_ok, entry_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(entry_ok, "{entry_output}");
            assert!(!entry_output.contains("1 = 0"), "{entry_output}");

            let (chapter_ok, chapter_output) = run_source_code_in_file_with_ok(
                root.join("chap7.lit")
                    .to_str()
                    .expect("fixture path is UTF-8"),
            );
            assert!(chapter_ok, "{chapter_output}");
            assert!(
                chapter_output.contains("result = chap6::base"),
                "{chapter_output}"
            );

            let python_output = crate::to_python::to_python_from_file_after_builtins(
                root.join("python_chapter.lit")
                    .to_str()
                    .expect("fixture path is UTF-8"),
            )
            .unwrap_or_else(|error| panic!("project chapter Python failed: {error:?}"));
            assert_eq!(python_output, "answer = 1.0");
        });
    }

    #[test]
    fn trust_local_import_skips_checks_but_strict_mode_rejects_it() {
        run_repository_test_with_large_stack("trust_local_import", || {
            let root = repository_test_dir("trust-local-import");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_project_config(&root, "./book.lit", &[("chap10", "./chap10.lit")]);
            write_file(&root.join("chap10.lit"), "have bad N = -1\n");

            write_file(
                &root.join("book.lit"),
                "local_import chap10\nchap10::bad = -1\n",
            );
            let (ordinary_ok, ordinary_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!ordinary_ok, "{ordinary_output}");

            write_file(
                &root.join("book.lit"),
                "trust local_import chap10\nchap10::bad = -1\n",
            );
            let (trusted_ok, trusted_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                true,
            );
            assert!(trusted_ok, "{trusted_output}");
            assert!(
                trusted_output.contains("\"trust_dependencies\"")
                    && trusted_output.contains("\"trust_local_import\": 1"),
                "{trusted_output}"
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
                strict_output.contains("strict mode does not allow trusted imports"),
                "{strict_output}"
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
            write_file(&root.join("book.lit"), "local_import chapter\n");

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
    fn trust_import_is_transitive_and_cannot_be_reused_as_verified() {
        run_repository_test_with_large_stack("trust_import", || {
            let root = repository_test_dir("trust-import");
            let a = root.join("A");
            fs::create_dir_all(&a).expect("create repository fixture");
            write_project_config(&root, "./book.lit", &[("A", "./A")]);
            write_project_config(&a, "./main.lit", &[("chap10", "./chap10.lit")]);
            write_file(&a.join("main.lit"), "local_import chap10\n");
            write_file(
                &a.join("chap10.lit"),
                "abstract_prop trusted_prop(x)\n\nthm trusted_all:\n    prove:\n        forall x R:\n            =>:\n                $trusted_prop(x)\n",
            );

            write_file(
                &root.join("book.lit"),
                "trust import A\nby thm A::chap10::trusted_all(2)\n$A::chap10::trusted_prop(2)\n",
            );
            let (trusted_ok, trusted_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(trusted_ok, "{trusted_output}");

            write_file(&root.join("book.lit"), "trust import A\nimport A\n");
            let (mixed_ok, mixed_output) = run_repository_with_output(
                root.to_str().expect("fixture path is UTF-8"),
                true,
                false,
                OutputLanguage::English,
                false,
            );
            assert!(!mixed_ok, "{mixed_output}");
            assert!(
                mixed_output.contains("already loaded through trust import"),
                "{mixed_output}"
            );

            let mut runtime = Runtime::new_with_builtin_code();
            discover_repository(&mut runtime, root.to_str().expect("fixture path is UTF-8"))
                .expect("discover trusted fixture");
            let entry = runtime.current_module_id();
            let (results, error) = crate::pipeline::run_repository_file_target(
                &mut runtime,
                RepositoryFileTarget::Entrance(entry),
            );
            assert!(error.is_some(), "mixed fixture should fail");
            let trust_summary = runtime.proof_trust_summary_from_stmt_results(&results);
            assert!(
                trust_summary
                    .dependencies
                    .iter()
                    .any(|dependency| dependency.kind == "trust_import"),
                "trusted import must taint the run summary"
            );
        });
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

    fn write_project_config(root: &Path, entrance: &str, exports: &[(&str, &str)]) {
        let mut content = format!("[entrance]\nfile = \"{}\"\n", entrance);
        if !exports.is_empty() {
            content.push_str("\n[export]\n");
            for (name, path) in exports {
                content.push_str(format!("{} = \"{}\"\n", name, path).as_str());
            }
        }
        write_file(&root.join("litex.config"), content.as_str());
    }
}
