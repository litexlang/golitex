use crate::prelude::*;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;

const MOD_DOT_LIT: &str = "mod.lit";
const MAIN_DOT_LIT: &str = "main.lit";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FileNode {
    module_id: ModuleId,
    file_id: FileEnvId,
}

pub fn discover_repository(
    runtime: &mut Runtime,
    repository_path: &str,
) -> Result<String, RuntimeError> {
    let repository_root = canonical_directory(repository_path, repository_path, 0)?;
    let mod_lit_path = repository_root.join(MOD_DOT_LIT);
    let main_lit_path = repository_root.join(MAIN_DOT_LIT);
    require_file(
        &mod_lit_path,
        format!(
            "repository `{}` does not contain {}",
            repository_root.to_string_lossy(),
            MOD_DOT_LIT
        ),
        repository_path,
        0,
    )?;
    require_file(
        &main_lit_path,
        format!(
            "repository `{}` does not contain {}",
            repository_root.to_string_lossy(),
            MAIN_DOT_LIT
        ),
        repository_path,
        0,
    )?;

    let repository_root_string = path_string(&repository_root, repository_path, 0)?;
    let main_lit_string = path_string(&main_lit_path, repository_path, 0)?;
    let root_module_id = runtime
        .new_repository_path_new_env_new_name_scope(repository_root_string, main_lit_string.clone())
        .map_err(|message| repository_error(message, repository_path, 0))?;

    discover_module_manifest(runtime, root_module_id, &mod_lit_path)?;
    let module_import_edges = scan_repository_dependencies(runtime)?;
    reject_cyclic_local_imports(runtime)?;
    reject_cyclic_module_imports(runtime, &module_import_edges)?;
    Ok(main_lit_string)
}

fn discover_module_manifest(
    runtime: &mut Runtime,
    module_id: ModuleId,
    mod_lit_path: &Path,
) -> Result<(), RuntimeError> {
    let content = fs::read_to_string(mod_lit_path).map_err(|error| {
        repository_error(
            format!(
                "failed to read {}: {}",
                mod_lit_path.to_string_lossy(),
                error
            ),
            &mod_lit_path.to_string_lossy(),
            0,
        )
    })?;
    let mod_lit_string = path_string(mod_lit_path, &mod_lit_path.to_string_lossy(), 0)?;
    let mut tokenizer = Tokenizer::new();
    let blocks = tokenizer.parse_blocks(&content, Rc::from(mod_lit_string.as_str()))?;

    for mut block in blocks {
        if !block.body.is_empty() {
            return Err(repository_error(
                "export declarations cannot have a body".to_string(),
                mod_lit_string.as_str(),
                block.line_file.0,
            ));
        }
        if block.header.first().map(String::as_str) != Some(EXPORT) {
            return Err(repository_error(
                "mod.lit is declarative and may contain only `export file` or `export mod` declarations"
                    .to_string(),
                mod_lit_string.as_str(),
                block.line_file.0,
            ));
        }
        let statement = runtime.parse_stmt(&mut block)?;
        let Stmt::Command(CommandStmt::ExportStmt(export)) = statement else {
            unreachable!("export parser should produce an export statement")
        };
        discover_export(runtime, module_id, export)?;
    }

    Ok(())
}

fn discover_export(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    export: ExportStmt,
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
            format!("duplicate export name `{}` in the same module", export.name),
            export.line_file.1.as_ref(),
            export.line_file.0,
        ));
    }

    let target_path = owner_root.join(&export.path);
    match export.kind {
        ExportKind::File => {
            let canonical_path = canonical_file(
                &target_path,
                export.line_file.1.as_ref(),
                export.line_file.0,
            )?;
            if canonical_path
                .extension()
                .and_then(|extension| extension.to_str())
                != Some("lit")
            {
                return Err(repository_error(
                    "export file must point to a .lit file".to_string(),
                    export.line_file.1.as_ref(),
                    export.line_file.0,
                ));
            }
            if canonical_path.file_name().and_then(|name| name.to_str()) == Some(MOD_DOT_LIT) {
                return Err(repository_error(
                    "mod.lit is a module declaration file and cannot be exported as a source file"
                        .to_string(),
                    export.line_file.1.as_ref(),
                    export.line_file.0,
                ));
            }
            let source_path = path_string(
                &canonical_path,
                export.line_file.1.as_ref(),
                export.line_file.0,
            )?;
            let canonical_name = join_module_name(&owner_name, &export.name);
            let file_id = runtime
                .module_manager
                .module_mut(owner_module_id)
                .expect("manifest owner module should exist")
                .create_exported_file_environment(source_path.clone(), canonical_name.clone());
            let target = ImportTarget::File {
                module_id: owner_module_id,
                file_id,
            };
            runtime
                .module_manager
                .register_exported_file(canonical_name, source_path, target)
                .map_err(|message| {
                    repository_error(message, export.line_file.1.as_ref(), export.line_file.0)
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
                        repository_error(message, export.line_file.1.as_ref(), export.line_file.0)
                    })?;
            }
        }
        ExportKind::Module => {
            let canonical_root = canonical_directory(
                &target_path.to_string_lossy(),
                export.line_file.1.as_ref(),
                export.line_file.0,
            )?;
            let child_mod_lit = canonical_root.join(MOD_DOT_LIT);
            let child_main_lit = canonical_root.join(MAIN_DOT_LIT);
            require_file(
                &child_mod_lit,
                format!(
                    "exported module directory `{}` does not contain {}",
                    canonical_root.to_string_lossy(),
                    MOD_DOT_LIT
                ),
                export.line_file.1.as_ref(),
                export.line_file.0,
            )?;
            require_file(
                &child_main_lit,
                format!(
                    "exported module directory `{}` does not contain {}",
                    canonical_root.to_string_lossy(),
                    MAIN_DOT_LIT
                ),
                export.line_file.1.as_ref(),
                export.line_file.0,
            )?;
            let child_name = join_module_name(&owner_name, &export.name);
            let child_root_string = path_string(
                &canonical_root,
                export.line_file.1.as_ref(),
                export.line_file.0,
            )?;
            let child_main_string = path_string(
                &child_main_lit,
                export.line_file.1.as_ref(),
                export.line_file.0,
            )?;
            let child_module_id = runtime
                .module_manager
                .create_discovered_module(child_name, child_root_string, child_main_string)
                .map_err(|message| {
                    repository_error(message, export.line_file.1.as_ref(), export.line_file.0)
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
                        repository_error(message, export.line_file.1.as_ref(), export.line_file.0)
                    })?;
            }
            discover_module_manifest(runtime, child_module_id, &child_mod_lit)?;
        }
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
        let (main_path, exported_files, exported_modules) = {
            let module = runtime
                .module_manager
                .module(module_id)
                .expect("discovered module should exist");
            let files = module
                .file_environments
                .iter()
                .filter(|file| file.kind == FileEnvironmentKind::Exported)
                .map(|file| (file.id, file.source_path.clone()))
                .collect::<Vec<(FileEnvId, String)>>();
            let modules = module
                .exports
                .values()
                .filter_map(|export| match export {
                    ExportEntry::Module { module_id, .. } => Some(*module_id),
                    ExportEntry::File { .. } => None,
                })
                .collect::<Vec<ModuleId>>();
            (module.main_file_path.clone(), files, modules)
        };

        let (main_imports, main_module_imports) =
            scan_source_dependencies(runtime, module_id, &main_path)?;
        let main_edges = module_import_edges
            .entry(module_id)
            .or_insert_with(Vec::new);
        main_edges.extend(exported_modules);
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
                .and_then(|module| module.file_environment_mut(file_id))
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
                "export is declarative and can only appear in mod.lit".to_string(),
                source_path,
                block.line_file.0,
            ));
        }
        if first_token == Some(IMPORT) {
            let statement = runtime.parse_import_stmt(&mut block)?;
            let Stmt::Command(CommandStmt::ImportStmt(import)) = statement else {
                unreachable!("import parser should produce an import statement")
            };
            match import {
                ImportStmt::ImportRelativePath(_) => {
                    return Err(repository_error(
                        "repository mode import must name a root export or globally registered module; use mod.lit and local_import for module-local dependencies"
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
        if first_token != Some(LOCAL_IMPORT) {
            continue;
        }
        if !block.body.is_empty() {
            return Err(repository_error(
                "local_import cannot have a body".to_string(),
                source_path,
                block.line_file.0,
            ));
        }
        let statement = runtime.parse_local_import_stmt(&mut block)?;
        let Stmt::Command(CommandStmt::LocalImportStmt(local_import)) = statement else {
            unreachable!("local_import parser should produce a local import statement")
        };
        let target = runtime
            .module_manager
            .module(owner_module_id)
            .and_then(|module| module.exports.get(&local_import.name))
            .map(|entry| entry.target(owner_module_id))
            .ok_or_else(|| {
                repository_error(
                    format!(
                        "local_import `{}` is not declared by this module's mod.lit",
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
        if block.header.first().map(String::as_str) == Some(LOCAL_IMPORT) {
            return Err(repository_error(
                "local_import is only allowed as a top-level source statement".to_string(),
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
        for file in module
            .file_environments
            .iter()
            .filter(|file| file.kind == FileEnvironmentKind::Exported)
        {
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
                .and_then(|module| module.file_environment(node.file_id))
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
        .and_then(|module| module.file_environment(node.file_id))
        .and_then(|file| file.canonical_name.clone())
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
                "exported file `{}` does not exist: {}",
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
                "export file path `{}` is not a file",
                path.to_string_lossy()
            ),
            source_path,
            line,
        ));
    }
    Ok(canonical)
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
            write_file(&root.join("mod.lit"), "export mod \"./A\" as A\n");
            write_file(
                &root.join("main.lit"),
                "import A\n\nA::chapters::leaf::x = 1\n",
            );
            write_file(
                &a.join("mod.lit"),
                "export file \"./chap2.lit\" as chap2\nexport file \"./chap3.lit\" as chap3\nexport mod \"./chapters\" as chapters\n",
            );
            write_file(&a.join("main.lit"), "local_import chap3\n\nchap3::z = 1\n");
            write_file(&a.join("chap2.lit"), "have x R = 1\n");
            write_file(
                &a.join("chap3.lit"),
                "local_import chap2\n\nhave z R = chap2::x\n",
            );
            write_file(
                &chapters.join("mod.lit"),
                "export file \"./leaf.lit\" as leaf\n",
            );
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
    fn repository_discovery_rejects_local_import_cycles_before_execution() {
        run_repository_test_with_large_stack("repository_cycle", || {
            let root = repository_test_dir("cycle");
            fs::create_dir_all(&root).expect("create repository fixture");
            write_file(
                &root.join("mod.lit"),
                "export file \"./a.lit\" as a\nexport file \"./b.lit\" as b\n",
            );
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
            write_file(
                &root.join("mod.lit"),
                "export mod \"./A\" as A\nexport mod \"./B\" as B\n",
            );
            write_file(&root.join("main.lit"), "import A\n");
            write_file(&a.join("mod.lit"), "");
            write_file(&a.join("main.lit"), "import B\n");
            write_file(&b.join("mod.lit"), "");
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
            write_file(
                &root.join("mod.lit"),
                "export file \"./shared.lit\" as shared\nexport mod \"./A\" as A\n",
            );
            write_file(
                &root.join("main.lit"),
                "local_import shared\nshared::root_x = 1\nimport A\n",
            );
            write_file(&root.join("shared.lit"), "have root_x R = 1\n");
            write_file(&a.join("mod.lit"), "");
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
    fn file_mode_rejects_manifests_exports_and_local_imports() {
        run_repository_test_with_large_stack("file_mode_module_syntax", || {
            let root = repository_test_dir("file-mode");
            fs::create_dir_all(&root).expect("create repository fixture");
            let manifest = root.join("mod.lit");
            let export_script = root.join("export-script.lit");
            let local_import_script = root.join("local-import-script.lit");
            write_file(&manifest, "export file \"./x.lit\" as x\n");
            write_file(&export_script, "export file \"./x.lit\" as x\n");
            write_file(&local_import_script, "local_import x\n");

            let (manifest_ok, manifest_output) =
                run_source_code_in_file_with_ok(manifest.to_str().expect("fixture path is UTF-8"));
            assert!(!manifest_ok, "{manifest_output}");
            assert!(
                manifest_output
                    .contains("mod.lit is a module declaration file; run the project with -r"),
                "{manifest_output}"
            );

            let (export_ok, export_output) = run_source_code_in_file_with_ok(
                export_script.to_str().expect("fixture path is UTF-8"),
            );
            assert!(!export_ok, "{export_output}");
            assert!(
                export_output.contains("export is unavailable in isolated file mode"),
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
}
