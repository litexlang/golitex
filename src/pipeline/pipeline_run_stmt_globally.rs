use crate::pipeline::run_source_code;
use crate::prelude::*;
use std::fs;
use std::path::{Component, Path, PathBuf};

fn resolve_run_file_path(user_path: &str, current_lit_file_path: &str) -> String {
    let user = Path::new(user_path);
    if user.is_absolute() {
        return user_path.to_string();
    }
    let current = Path::new(current_lit_file_path);
    let base_dir = current.parent().unwrap_or_else(|| Path::new(""));
    base_dir.join(user).to_string_lossy().into_owned()
}

pub fn run_stmt_at_global_env(
    stmt: &Stmt,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    match stmt {
        Stmt::Command(CommandStmt::RunFileStmt(run_file_stmt)) => {
            return run_file(run_file_stmt, runtime);
        }
        Stmt::Command(CommandStmt::ImportStmt(import_stmt)) => {
            return run_import_stmt(import_stmt, runtime);
        }
        _ => {
            return runtime.exec_stmt(stmt);
        }
    }
}

fn run_file(
    _run_file_stmt: &RunFileStmt,
    _runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    let current_lit_path = _runtime.module_manager.borrow().current_file_path_rc();
    let path = resolve_run_file_path(_run_file_stmt.file_path.as_str(), current_lit_path.as_ref());
    run_file_at_resolved_path(_run_file_stmt.clone().into(), path, _runtime)
}

fn run_file_at_resolved_path(
    stmt: Stmt,
    path: String,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    let content = fs::read_to_string(path.as_str()).map_err(|_| {
        RuntimeError::ExecStmtError({
            let lf = stmt.line_file();
            RuntimeErrorStruct::new(
                Some(stmt.clone()),
                format!("Failed to read file: {}", path.as_str()),
                lf,
                None,
                vec![],
            )
        })
    })?;

    let current_source_path = runtime.module_manager.borrow().current_file_path_rc();
    runtime.new_file_and_update_runtime_with_file_content(path.as_str());

    let result = run_source_code(content.as_str(), runtime);

    runtime.set_current_source_path_rc(current_source_path);

    if let Some(error) = result.1 {
        return Err(error);
    };

    return Ok((NonFactualStmtSuccess::new(stmt, InferResult::new(), result.0)).into());
}

fn candidate_std_roots() -> Vec<PathBuf> {
    let env_std_path = std::env::var_os("LITEX_STD_PATH").map(PathBuf::from);
    let current_exe = std::env::current_exe().ok();
    let local_app_data = std::env::var_os("LOCALAPPDATA").map(PathBuf::from);
    let program_files = std::env::var_os("ProgramFiles").map(PathBuf::from);

    candidate_std_roots_from(env_std_path, current_exe, local_app_data, program_files)
}

fn candidate_std_roots_from(
    env_std_path: Option<PathBuf>,
    current_exe: Option<PathBuf>,
    local_app_data: Option<PathBuf>,
    program_files: Option<PathBuf>,
) -> Vec<PathBuf> {
    let mut roots: Vec<PathBuf> = Vec::new();

    if let Some(env_std_path) = env_std_path {
        push_std_root_if_new(&mut roots, env_std_path);
    }

    push_std_root_if_new(&mut roots, PathBuf::from("std"));

    if let Some(current_exe) = current_exe {
        let exe_dir = current_exe.parent().unwrap_or_else(|| Path::new(""));
        for ancestor in exe_dir.ancestors() {
            push_std_root_if_new(&mut roots, ancestor.join("std"));
            push_std_root_if_new(&mut roots, ancestor.join("share").join("litex").join("std"));
        }
    }

    push_std_root_if_new(
        &mut roots,
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("std"),
    );

    push_std_root_if_new(&mut roots, PathBuf::from("/opt/homebrew/share/litex/std"));
    push_std_root_if_new(&mut roots, PathBuf::from("/usr/local/share/litex/std"));
    push_std_root_if_new(&mut roots, PathBuf::from("/usr/share/litex/std"));

    if let Some(local_app_data) = local_app_data {
        push_std_root_if_new(&mut roots, local_app_data.join("litex").join("std"));
    }

    if let Some(program_files) = program_files {
        push_std_root_if_new(&mut roots, program_files.join("Litex").join("std"));
    }

    roots
}

fn push_std_root_if_new(roots: &mut Vec<PathBuf>, candidate: PathBuf) {
    let candidate_string = candidate.to_string_lossy().into_owned();
    if roots
        .iter()
        .all(|existing| existing.to_string_lossy() != candidate_string)
    {
        roots.push(candidate);
    }
}

fn run_import_stmt(
    import_stmt: &ImportStmt,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    let import_info = imported_module_info(import_stmt, runtime)?;
    let importing_module_name = runtime.module_manager.borrow().current_module_name.clone();
    let reactivate_existing = runtime
        .module_manager
        .borrow()
        .imported_module_can_be_loaded_or_reactivated(
            &import_info.module_name,
            &import_info.module_root_path,
        )
        .map_err(|msg| import_name_already_used_error(import_stmt, msg))?;
    if reactivate_existing {
        runtime
            .module_manager
            .borrow_mut()
            .reactivate_imported_module(&import_info.module_name);
        runtime
            .module_manager
            .borrow_mut()
            .record_import_dependency(&importing_module_name, &import_info.module_name);
        return Ok(NonFactualStmtSuccess::new_with_stmt(import_stmt.clone().into()).into());
    }
    // Imported-module runtimes share this ModuleManager with the parent runtime.
    // Loading an import can therefore mutate parent-visible state before the import
    // finishes, for example by registering nested imports or changing file context.
    // If any later step fails, restore this snapshot so a failed import leaves no
    // partial module state behind.
    let module_manager_before_import = runtime.module_manager.borrow().clone();
    if let Err(msg) = runtime
        .module_manager
        .borrow_mut()
        .begin_loading_import(&import_info.module_name, &import_info.module_root_path)
    {
        return Err(import_stmt_error(import_stmt, msg));
    }
    let environment = match load_imported_module_environment(
        import_stmt,
        &import_info.module_name,
        &import_info.module_root_path,
        &import_info.main_lit_path,
        runtime,
    ) {
        Ok(environment) => environment,
        Err(error) => {
            *runtime.module_manager.borrow_mut() = module_manager_before_import;
            return Err(error);
        }
    };
    runtime
        .module_manager
        .borrow_mut()
        .finish_loading_import(&import_info.module_name, &import_info.module_root_path);
    let imported_module_name = import_info.module_name.clone();
    let register_result = runtime
        .module_manager
        .borrow_mut()
        .register_imported_module(
            import_info.module_name,
            import_info.module_root_path,
            environment,
            import_info.is_std,
        );
    if let Err(msg) = register_result {
        *runtime.module_manager.borrow_mut() = module_manager_before_import;
        return Err(import_name_already_used_error(import_stmt, msg));
    }
    runtime
        .module_manager
        .borrow_mut()
        .record_import_dependency(&importing_module_name, &imported_module_name);

    Ok(NonFactualStmtSuccess::new_with_stmt(import_stmt.clone().into()).into())
}

fn load_imported_module_environment(
    import_stmt: &ImportStmt,
    module_name: &str,
    module_root_path: &str,
    main_lit_path: &str,
    parent_runtime: &Runtime,
) -> Result<Environment, RuntimeError> {
    let content = fs::read_to_string(main_lit_path).map_err(|_| {
        import_stmt_error(
            import_stmt,
            format!(
                "Failed to read imported module entry file: {}",
                main_lit_path
            ),
        )
    })?;

    let parent_context = {
        let module_manager = parent_runtime.module_manager.borrow();
        (
            module_manager.current_file_path_rc(),
            module_manager.entry_path_rc.clone(),
            module_manager.current_module_name.clone(),
            module_manager.current_module_path.clone(),
        )
    };

    let mut module_runtime = Runtime::new_for_import_from_parent(parent_runtime);
    module_runtime.new_file_path_new_env_new_name_scope(main_lit_path);
    {
        let mut module_manager = module_runtime.module_manager.borrow_mut();
        module_manager.current_module_name = module_name.to_string();
        module_manager.current_module_path = module_root_path.to_string();
    }

    let (_stmt_results, runtime_error) = run_source_code(content.as_str(), &mut module_runtime);
    if let Some(error) = runtime_error {
        return Err(short_exec_error(
            import_stmt.clone().into(),
            format!(
                "failed to import module `{}` from `{}`",
                module_name, module_root_path
            ),
            Some(error),
            vec![],
        ));
    }

    let Some(module_env) = module_runtime.environment_stack.pop() else {
        return Err(import_stmt_error(
            import_stmt,
            format!(
                "imported module `{}` did not produce an environment",
                module_name
            ),
        ));
    };
    {
        let mut module_manager = parent_runtime.module_manager.borrow_mut();
        module_manager.current_source_path_rc = parent_context.0;
        module_manager.entry_path_rc = parent_context.1;
        module_manager.current_module_name = parent_context.2;
        module_manager.current_module_path = parent_context.3;
    }
    Ok(*module_env)
}

struct ImportModuleInfo {
    module_name: String,
    module_root_path: String,
    main_lit_path: String,
    is_std: bool,
}

impl ImportModuleInfo {
    fn new(
        module_name: String,
        module_root_path: String,
        main_lit_path: String,
        is_std: bool,
    ) -> Self {
        ImportModuleInfo {
            module_name,
            module_root_path,
            main_lit_path,
            is_std,
        }
    }
}

fn imported_module_info(
    import_stmt: &ImportStmt,
    runtime: &Runtime,
) -> Result<ImportModuleInfo, RuntimeError> {
    match import_stmt {
        ImportStmt::ImportRelativePath(stmt) => {
            let current_lit_path = runtime.module_manager.borrow().current_file_path_rc();
            let path = resolve_run_file_path(stmt.path.as_str(), current_lit_path.as_ref());
            let relative_entry = relative_import_entry(path.as_str(), import_stmt)?;
            let module_name = match stmt.as_mod_name.as_ref() {
                Some(name) => {
                    let module_name = validate_import_module_name(name.clone(), import_stmt)?;
                    validate_relative_import_alias_not_std_module(&module_name, import_stmt)?;
                    module_name
                }
                None => {
                    if relative_entry.is_lit_file {
                        return Err(import_stmt_error(
                            import_stmt,
                            format!(
                                "importing a .lit file requires an explicit module alias, for example import \"{}\" as M",
                                stmt.path
                            ),
                        ));
                    }
                    validate_import_module_name(
                        module_name_from_path(&stmt.path, import_stmt)?,
                        import_stmt,
                    )?
                }
            };
            Ok(ImportModuleInfo::new(
                module_name,
                relative_entry.module_root_path,
                relative_entry.main_lit_path,
                false,
            ))
        }
        ImportStmt::ImportGlobalModule(stmt) => {
            let module_name = validate_import_module_name(stmt.mod_name.clone(), import_stmt)?;
            let (module_root_path, main_lit_path) = std_import_paths(stmt.mod_name.as_str());
            Ok(ImportModuleInfo::new(
                module_name,
                module_root_path,
                main_lit_path,
                true,
            ))
        }
    }
}

struct RelativeImportEntry {
    module_root_path: String,
    main_lit_path: String,
    is_lit_file: bool,
}

impl RelativeImportEntry {
    fn new(module_root_path: String, main_lit_path: String, is_lit_file: bool) -> Self {
        RelativeImportEntry {
            module_root_path,
            main_lit_path,
            is_lit_file,
        }
    }
}

fn relative_import_entry(
    path: &str,
    import_stmt: &ImportStmt,
) -> Result<RelativeImportEntry, RuntimeError> {
    let module_root_path = absolute_path_string(PathBuf::from(path));
    let module_root = Path::new(&module_root_path);

    if module_root.extension().and_then(|ext| ext.to_str()) == Some("lit") {
        if !module_root.is_file() {
            return Err(import_stmt_error(
                import_stmt,
                format!(
                    "imported .lit file does not exist: {}",
                    module_root.to_string_lossy()
                ),
            ));
        }
        return Ok(RelativeImportEntry::new(
            module_root_path.clone(),
            module_root_path,
            true,
        ));
    }

    validate_import_module_root(module_root, import_stmt)?;
    let main_lit_path = absolute_path_string(module_root.join("main.lit"));
    Ok(RelativeImportEntry::new(
        module_root_path,
        main_lit_path,
        false,
    ))
}

fn validate_import_module_name(
    name: String,
    import_stmt: &ImportStmt,
) -> Result<String, RuntimeError> {
    if let Err(msg) = is_valid_litex_name(name.as_str()) {
        return Err(import_stmt_error(
            import_stmt,
            format!("invalid import module name `{}`: {}", name, msg),
        ));
    }
    Ok(name)
}

fn validate_relative_import_alias_not_std_module(
    name: &str,
    import_stmt: &ImportStmt,
) -> Result<(), RuntimeError> {
    if std_module_exists(name) {
        return Err(import_stmt_error(
            import_stmt,
            format!(
                "relative import alias `{}` conflicts with standard-library module `{}`; use a different alias",
                name, name
            ),
        ));
    }
    Ok(())
}

fn module_name_from_path(path: &str, import_stmt: &ImportStmt) -> Result<String, RuntimeError> {
    match Path::new(path).file_name() {
        Some(stem) => Ok(stem.to_string_lossy().into_owned()),
        None => Err(import_stmt_error(
            import_stmt,
            format!(
                "cannot infer import module name from path `{}`; use `as <name>`",
                path
            ),
        )),
    }
}

fn validate_import_module_root(
    module_root: &Path,
    import_stmt: &ImportStmt,
) -> Result<(), RuntimeError> {
    if module_root.is_file() {
        return Err(import_stmt_error(
            import_stmt,
            format!(
                "import expects a module directory containing main.lit or a .lit file, not a file: {}",
                module_root.to_string_lossy()
            ),
        ));
    }
    let main_lit = module_root.join("main.lit");
    if !main_lit.is_file() {
        return Err(import_stmt_error(
            import_stmt,
            format!(
                "import module directory `{}` does not contain main.lit",
                module_root.to_string_lossy()
            ),
        ));
    }
    Ok(())
}

fn std_module_exists(module_name: &str) -> bool {
    for std_root in candidate_std_roots() {
        if std_root.join(module_name).join("main.lit").is_file() {
            return true;
        }
    }
    false
}

fn std_import_paths(module_name: &str) -> (String, String) {
    for std_root in candidate_std_roots() {
        let module_root = std_root.join(module_name);
        let main_lit = module_root.join("main.lit");
        if main_lit.is_file() {
            return (
                absolute_path_string(module_root),
                absolute_path_string(main_lit),
            );
        }
    }

    let module_root = Path::new("std").join(module_name);
    let main_lit = module_root.join("main.lit");
    (
        absolute_path_string(module_root),
        absolute_path_string(main_lit),
    )
}

fn absolute_path_string(path: PathBuf) -> String {
    let absolute_path = if path.is_absolute() {
        path
    } else {
        match std::env::current_dir() {
            Ok(current_dir) => current_dir.join(path),
            Err(_) => path,
        }
    };

    normalize_path(absolute_path).to_string_lossy().into_owned()
}

fn normalize_path(path: PathBuf) -> PathBuf {
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => match normalized.components().last() {
                Some(Component::Normal(_)) => {
                    normalized.pop();
                }
                Some(Component::RootDir) | Some(Component::Prefix(_)) => {}
                _ => normalized.push(component.as_os_str()),
            },
            _ => normalized.push(component.as_os_str()),
        }
    }
    normalized
}

fn import_stmt_error(import_stmt: &ImportStmt, message: String) -> RuntimeError {
    let stmt: Stmt = import_stmt.clone().into();
    short_exec_error(stmt, message, None, vec![])
}

fn import_name_already_used_error(import_stmt: &ImportStmt, message: String) -> RuntimeError {
    let stmt: Stmt = import_stmt.clone().into();
    let line_file = stmt.line_file();
    NameAlreadyUsedRuntimeError(RuntimeErrorStruct::new(
        Some(stmt),
        message,
        line_file,
        None,
        vec![],
    ))
    .into()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_test_dir(test_name: &str) -> PathBuf {
        let dir =
            std::env::temp_dir().join(format!("litex-import-{}-{}", test_name, std::process::id()));
        fs::create_dir_all(&dir).expect("create temp import test dir");
        dir
    }

    fn write_temp_module(test_name: &str, content: &str) -> PathBuf {
        let dir = temp_test_dir(test_name);
        fs::write(dir.join("main.lit"), content).expect("write temp module");
        dir
    }

    fn write_temp_lit_file(test_name: &str, file_name: &str, content: &str) -> PathBuf {
        let dir = temp_test_dir(test_name);
        let file_path = dir.join(file_name);
        fs::write(&file_path, content).expect("write temp .lit file");
        file_path
    }

    const LARGE_IMPORT_TEST_STACK_SIZE: usize = 64 * 1024 * 1024;

    fn run_import_test_with_large_stack(test_name: &str, f: impl FnOnce() + Send + 'static) {
        std::thread::Builder::new()
            .name(test_name.to_string())
            .stack_size(LARGE_IMPORT_TEST_STACK_SIZE)
            .spawn(f)
            .expect("spawn large-stack import test")
            .join()
            .unwrap();
    }

    #[test]
    fn std_roots_include_installed_layouts() {
        let env_root = PathBuf::from("/custom/litex/std");
        let exe_path = PathBuf::from("/opt/litex/bin/litex");
        let local_app_data = PathBuf::from(r"C:\Users\me\AppData\Local");
        let program_files = PathBuf::from(r"C:\Program Files");

        let roots = candidate_std_roots_from(
            Some(env_root.clone()),
            Some(exe_path),
            Some(local_app_data.clone()),
            Some(program_files.clone()),
        );

        assert_eq!(roots.first(), Some(&env_root));
        assert!(roots.contains(&PathBuf::from("std")));
        assert!(roots.contains(&PathBuf::from("/opt/litex/bin/std")));
        assert!(roots.contains(&PathBuf::from("/opt/litex/share/litex/std")));
        assert!(roots.contains(&PathBuf::from("/usr/share/litex/std")));
        assert!(roots.contains(&local_app_data.join("litex").join("std")));
        assert!(roots.contains(&program_files.join("Litex").join("std")));
    }

    #[test]
    fn import_relative_path_registers_module_info() {
        let entry_path = std::env::temp_dir()
            .join("litex-import-entry")
            .join("entry.lit");
        let module_dir = entry_path.parent().unwrap().join("module");
        let module_path = module_dir.join("main.lit");
        fs::create_dir_all(&module_dir).expect("create temp module dir");
        fs::write(&module_path, "abstract_prop loaded_prop(x)").expect("write temp module");
        let expected_path = module_dir.to_string_lossy().into_owned();

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(entry_path.to_string_lossy().as_ref());

        let (_, runtime_error) = run_source_code("import \"module\" as demo", &mut runtime);

        assert!(runtime_error.is_none());
        let module_manager = runtime.module_manager.borrow();
        let imported = module_manager.imported_modules.get("demo").unwrap();
        assert_eq!(imported.absolute_path, expected_path);
        assert!(!imported.is_std);
        assert!(imported
            .environment
            .defined_abstract_props
            .contains_key("loaded_prop"));
    }

    #[test]
    fn import_std_module_registers_module_info() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code("import Trig", &mut runtime);

        assert!(runtime_error.is_none());
        let module_manager = runtime.module_manager.borrow();
        let imported = module_manager.imported_modules.get("Trig").unwrap();
        assert!(imported.is_std);
        assert!(imported.absolute_path.contains("Trig"));
        assert_eq!(
            Path::new(imported.absolute_path.as_str())
                .file_name()
                .and_then(|name| name.to_str()),
            Some("Trig")
        );
        assert!(imported
            .environment
            .defined_def_props
            .contains_key("strictly_increasing_on"));
    }

    #[test]
    fn import_std_module_with_as_is_rejected() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code("import Trig as trig", &mut runtime);

        let runtime_error = runtime_error.expect("std import alias should fail");
        let output = format!("{:?}", runtime_error);
        assert!(
            output.contains("standard-library imports use the std folder name"),
            "std import alias should report folder-name requirement, got: {}",
            output
        );
        assert!(runtime.module_manager.borrow().imported_modules.is_empty());
    }

    #[test]
    fn import_relative_path_alias_matching_std_module_is_rejected() {
        let path = write_temp_module("relative-import-std-alias", "abstract_prop p(x)");
        let source_code = format!("import \"{}\" as Nat", path.to_string_lossy());
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);

        let runtime_error = runtime_error.expect("relative import std alias should fail");
        let output = format!("{:?}", runtime_error);
        assert!(
            output.contains(
                "relative import alias `Nat` conflicts with standard-library module `Nat`"
            ),
            "relative import std alias should report std-name conflict, got: {}",
            output
        );
        assert!(runtime.module_manager.borrow().imported_modules.is_empty());
    }

    #[test]
    fn import_std_module_without_as_uses_module_name() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code("import ZMod", &mut runtime);

        assert!(runtime_error.is_none());
        let module_manager = runtime.module_manager.borrow();
        let imported = module_manager.imported_modules.get("ZMod").unwrap();
        assert!(imported.is_std);
        assert_eq!(
            Path::new(imported.absolute_path.as_str())
                .file_name()
                .and_then(|name| name.to_str()),
            Some("ZMod")
        );
    }

    #[test]
    fn import_same_module_name_and_path_is_idempotent() {
        let path = write_temp_module("idempotent-same-import", "abstract_prop p(x)");
        let source_code = format!(
            "import \"{}\" as Same\nimport \"{}\" as Same",
            path.to_string_lossy(),
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);

        assert!(runtime_error.is_none());
        let module_manager = runtime.module_manager.borrow();
        assert_eq!(module_manager.imported_modules.len(), 1);
        assert!(module_manager.imported_modules.contains_key("Same"));
        assert!(!module_manager.stopped_module.contains("Same"));
    }

    #[test]
    fn nested_import_updates_shared_module_manager() {
        let root = temp_test_dir("nested-import-shared-manager");
        let nested_dir = root.join("Nested");
        let child_dir = root.join("Child");
        fs::create_dir_all(&nested_dir).expect("create nested module dir");
        fs::create_dir_all(&child_dir).expect("create child module dir");
        fs::write(
            nested_dir.join("main.lit"),
            "abstract_prop nested_prop(x)\nknow $nested_prop(2)",
        )
        .expect("write nested module");
        fs::write(
            child_dir.join("main.lit"),
            "import \"../Nested\" as Nested\nabstract_prop child_prop(x)",
        )
        .expect("write child module");

        let source_code = format!(
            "import \"{}\" as Child\n$Nested::nested_prop(2)",
            child_dir.to_string_lossy()
        );
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);

        assert!(runtime_error.is_none());
        let module_manager = runtime.module_manager.borrow();
        assert!(module_manager.imported_modules.contains_key("Child"));
        assert!(module_manager.imported_modules.contains_key("Nested"));
        let child = module_manager.imported_modules.get("Child").unwrap();
        assert_eq!(child.import_dependencies, vec!["Nested".to_string()]);
    }

    #[test]
    fn nested_then_top_level_same_import_reuses_cached_module() {
        let root = temp_test_dir("nested-then-top-level-import-runs-once");
        let b_dir = root.join("B");
        let a_dir = root.join("A");
        fs::create_dir_all(&b_dir).expect("create B module dir");
        fs::create_dir_all(&a_dir).expect("create A module dir");
        fs::write(
            b_dir.join("main.lit"),
            "abstract_prop b_prop(x)\nknow $b_prop(2)",
        )
        .expect("write B module");
        fs::write(
            a_dir.join("main.lit"),
            "import \"../B\" as B\nabstract_prop a_prop(x)",
        )
        .expect("write A module");

        let source_code = format!(
            "import \"{}\" as A\nimport \"{}\" as B\n$B::b_prop(2)",
            a_dir.to_string_lossy(),
            b_dir.to_string_lossy()
        );
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "top-level reimport after nested import should succeed:\n{}",
            run_output
        );
        let module_manager = runtime.module_manager.borrow();
        assert_eq!(module_manager.imported_modules.len(), 2);
        assert!(module_manager.imported_modules.contains_key("A"));
        assert!(module_manager.imported_modules.contains_key("B"));
        let a = module_manager.imported_modules.get("A").unwrap();
        assert_eq!(a.import_dependencies, vec!["B".to_string()]);
    }

    #[test]
    fn reimport_cached_module_reactivates_nested_imports_after_clear() {
        let root = temp_test_dir("reimport-cached-module-reactivates-nested");
        let nested_dir = root.join("Nested");
        let child_dir = root.join("Child");
        fs::create_dir_all(&nested_dir).expect("create nested module dir");
        fs::create_dir_all(&child_dir).expect("create child module dir");
        fs::write(
            nested_dir.join("main.lit"),
            "abstract_prop nested_prop(x)\nknow $nested_prop(2)",
        )
        .expect("write nested module");
        fs::write(
            child_dir.join("main.lit"),
            "import \"../Nested\" as Nested\nabstract_prop child_prop(x)",
        )
        .expect("write child module");

        let source_code = format!(
            "import \"{}\" as Child\nclear\nimport \"{}\" as Child\n$Nested::nested_prop(2)",
            child_dir.to_string_lossy(),
            child_dir.to_string_lossy()
        );
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "reimport_cached_module_reactivates_nested_imports_after_clear",
        );

        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "reimporting Child should reactivate its Nested import:\n{}",
            run_output
        );
        let module_manager = runtime.module_manager.borrow();
        assert!(!module_manager.stopped_module.contains("Child"));
        assert!(!module_manager.stopped_module.contains("Nested"));
        let child = module_manager.imported_modules.get("Child").unwrap();
        assert_eq!(child.import_dependencies, vec!["Nested".to_string()]);
    }

    #[test]
    fn failed_nested_import_rolls_back_shared_module_manager() {
        let root = temp_test_dir("failed-nested-import-rolls-back-manager");
        let nested_dir = root.join("Nested");
        let child_dir = root.join("Child");
        fs::create_dir_all(&nested_dir).expect("create nested module dir");
        fs::create_dir_all(&child_dir).expect("create child module dir");
        fs::write(nested_dir.join("main.lit"), "abstract_prop nested_prop(x)")
            .expect("write nested module");
        fs::write(
            child_dir.join("main.lit"),
            "import \"../Nested\" as Nested\n$missing_prop(2)",
        )
        .expect("write child module");

        let source_code = format!("import \"{}\" as Child", child_dir.to_string_lossy());
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);

        assert!(runtime_error.is_some());
        assert!(runtime.module_manager.borrow().imported_modules.is_empty());
    }

    #[test]
    fn cyclic_import_is_rejected_and_rolls_back_shared_module_manager() {
        let root = temp_test_dir("cyclic-import-rolls-back-manager");
        let a_dir = root.join("A");
        let b_dir = root.join("B");
        fs::create_dir_all(&a_dir).expect("create A module dir");
        fs::create_dir_all(&b_dir).expect("create B module dir");
        fs::write(
            a_dir.join("main.lit"),
            "import \"../B\" as B\nabstract_prop a_prop(x)",
        )
        .expect("write A module");
        fs::write(
            b_dir.join("main.lit"),
            "import \"../A\" as A\nabstract_prop b_prop(x)",
        )
        .expect("write B module");

        let source_code = format!("import \"{}\" as A", a_dir.to_string_lossy());
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(!run_succeeded, "cyclic import should fail:\n{}", run_output);
        assert!(
            run_output.contains("cyclic import: A -> B -> A"),
            "cyclic import should report the import chain:\n{}",
            run_output
        );
        let module_manager = runtime.module_manager.borrow();
        assert!(module_manager.imported_modules.is_empty());
        assert!(module_manager.loading_import_stack.is_empty());
    }

    #[test]
    fn import_restores_parent_relative_path_context() {
        let root = temp_test_dir("import-restores-parent-relative-path");
        let entry_path = root.join("entry.lit");
        let child_dir = root.join("Child");
        let sibling_dir = root.join("Sibling");
        fs::create_dir_all(&child_dir).expect("create child module dir");
        fs::create_dir_all(&sibling_dir).expect("create sibling module dir");
        fs::write(child_dir.join("main.lit"), "abstract_prop child_prop(x)")
            .expect("write child module");
        fs::write(
            sibling_dir.join("main.lit"),
            "abstract_prop sibling_prop(x)",
        )
        .expect("write sibling module");

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(entry_path.to_string_lossy().as_ref());

        let (_, runtime_error) = run_source_code(
            "import \"Child\" as Child\nimport \"Sibling\" as Sibling",
            &mut runtime,
        );

        assert!(runtime_error.is_none());
        let module_manager = runtime.module_manager.borrow();
        assert!(module_manager.imported_modules.contains_key("Child"));
        assert!(module_manager.imported_modules.contains_key("Sibling"));
    }

    #[test]
    fn import_duplicate_module_name_is_rejected() {
        let first_path = write_temp_module("duplicate-name-first", "abstract_prop p(x)");
        let second_path = write_temp_module("duplicate-name-second", "abstract_prop q(x)");
        let source_code = format!(
            "import \"{}\" as duplicate\nimport \"{}\" as duplicate",
            first_path.to_string_lossy(),
            second_path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);

        let runtime_error = runtime_error.expect("duplicate module name should fail");
        match runtime_error {
            RuntimeError::NameAlreadyUsedError(error) => {
                assert!(error
                    .msg
                    .contains("module name `duplicate` has already been used"));
            }
            other => panic!("expected NameAlreadyUsedError, got {:?}", other),
        }
        let module_manager = runtime.module_manager.borrow();
        assert_eq!(module_manager.imported_modules.len(), 1);
        let imported = module_manager.imported_modules.get("duplicate").unwrap();
        assert_eq!(
            imported.absolute_path,
            first_path.to_string_lossy().into_owned()
        );
    }

    #[test]
    fn import_duplicate_module_path_is_rejected() {
        let path = write_temp_module("duplicate-path", "abstract_prop p(x)");
        let source_code = format!(
            "import \"{}\" as first_name\nimport \"{}\" as second_name",
            path.to_string_lossy(),
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);

        let runtime_error = runtime_error.expect("duplicate module path should fail");
        match runtime_error {
            RuntimeError::NameAlreadyUsedError(error) => {
                assert!(error
                    .msg
                    .contains("has already been imported as module name `first_name`"));
            }
            other => panic!("expected NameAlreadyUsedError, got {:?}", other),
        }
        let module_manager = runtime.module_manager.borrow();
        assert_eq!(module_manager.imported_modules.len(), 1);
        assert!(module_manager.imported_modules.contains_key("first_name"));
    }

    #[test]
    fn import_equivalent_relative_paths_are_rejected() {
        let entry_path = std::env::temp_dir()
            .join("litex-import-entry")
            .join("entry.lit");
        let module_dir = entry_path.parent().unwrap().join("module");
        fs::create_dir_all(&module_dir).expect("create temp module dir");
        fs::write(module_dir.join("main.lit"), "abstract_prop loaded_prop(x)")
            .expect("write temp module");

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(entry_path.to_string_lossy().as_ref());

        let (_, runtime_error) = run_source_code(
            "import \"module\" as demo\nimport \"./module\" as other_demo",
            &mut runtime,
        );

        let runtime_error = runtime_error.expect("equivalent relative module paths should fail");
        match runtime_error {
            RuntimeError::NameAlreadyUsedError(error) => {
                assert!(error
                    .msg
                    .contains("has already been imported as module name `demo`"));
            }
            other => panic!("expected NameAlreadyUsedError, got {:?}", other),
        }
        let module_manager = runtime.module_manager.borrow();
        assert_eq!(module_manager.imported_modules.len(), 1);
        assert!(module_manager.imported_modules.contains_key("demo"));
    }

    #[test]
    fn import_lit_file_path_registers_module_info() {
        run_import_test_with_large_stack("import_lit_file_path_registers_module_info", || {
            let file_path = write_temp_lit_file(
                "lit-file-path-registers-module",
                "chap6_sketch.lit",
                "abstract_prop loaded_prop(x)\nknow $loaded_prop(2)",
            );
            let source_code = format!(
                "import \"{}\" as chap6\n$chap6::loaded_prop(2)",
                file_path.to_string_lossy()
            );

            let mut runtime = Runtime::new_with_builtin_code();
            runtime
                .new_file_path_new_env_new_name_scope("import_lit_file_path_registers_module_info");
            let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
            let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
                &runtime,
                &stmt_results,
                &runtime_error,
                false,
            );

            assert!(run_succeeded, "file import should verify:\n{}", run_output);
            let module_manager = runtime.module_manager.borrow();
            let imported = module_manager.imported_modules.get("chap6").unwrap();
            assert_eq!(
                imported.absolute_path,
                file_path.to_string_lossy().into_owned()
            );
            assert!(!imported.is_std);
            assert!(imported
                .environment
                .defined_abstract_props
                .contains_key("loaded_prop"));
        });
    }

    #[test]
    fn import_lit_file_without_alias_is_rejected() {
        run_import_test_with_large_stack("import_lit_file_without_alias_is_rejected", || {
            let file_path =
                write_temp_lit_file("lit-file-without-alias-rejected", "chap6.lit", "1 = 1");
            let source_code = format!("import \"{}\"", file_path.to_string_lossy());

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("repl");

            let (_, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);

            let runtime_error = runtime_error.expect(".lit import without alias should fail");
            let output = format!("{:?}", runtime_error);
            assert!(
                output.contains("importing a .lit file requires an explicit module alias"),
                ".lit import without alias should report alias requirement, got: {}",
                output
            );
        });
    }

    #[test]
    fn import_equivalent_lit_file_paths_are_rejected() {
        run_import_test_with_large_stack("import_equivalent_lit_file_paths_are_rejected", || {
            let root = temp_test_dir("equivalent-lit-file-paths");
            let entry_path = root.join("entry.lit");
            let file_path = root.join("module.lit");
            fs::write(&file_path, "abstract_prop loaded_prop(x)").expect("write temp .lit file");

            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope(entry_path.to_string_lossy().as_ref());

            let (_, runtime_error) = run_source_code(
                "import \"module.lit\" as demo\nimport \"./module.lit\" as other_demo",
                &mut runtime,
            );

            let runtime_error = runtime_error.expect("equivalent relative .lit paths should fail");
            match runtime_error {
                RuntimeError::NameAlreadyUsedError(error) => {
                    assert!(error
                        .msg
                        .contains("has already been imported as module name `demo`"));
                }
                other => panic!("expected NameAlreadyUsedError, got {:?}", other),
            }
            let module_manager = runtime.module_manager.borrow();
            assert_eq!(module_manager.imported_modules.len(), 1);
            assert!(module_manager.imported_modules.contains_key("demo"));
        });
    }

    #[test]
    fn nested_lit_file_import_uses_imported_file_relative_path() {
        run_import_test_with_large_stack(
            "nested_lit_file_import_uses_imported_file_relative_path",
            || {
                let root = temp_test_dir("nested-lit-file-relative-path");
                let entry_path = root.join("entry.lit");
                let module_dir = root.join("module");
                fs::create_dir_all(&module_dir).expect("create temp module dir");
                fs::write(
                    module_dir.join("Nested.lit"),
                    "abstract_prop nested_prop(x)\nknow $nested_prop(2)",
                )
                .expect("write nested .lit file");
                fs::write(
                    module_dir.join("Child.lit"),
                    "import \"./Nested.lit\" as Nested\nabstract_prop child_prop(x)",
                )
                .expect("write child .lit file");

                let mut runtime = Runtime::new_with_builtin_code();
                runtime.new_file_path_new_env_new_name_scope(entry_path.to_string_lossy().as_ref());
                let (stmt_results, runtime_error) = run_source_code(
                    "import \"module/Child.lit\" as Child\n$Nested::nested_prop(2)",
                    &mut runtime,
                );
                let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
                    &runtime,
                    &stmt_results,
                    &runtime_error,
                    false,
                );

                assert!(
                    run_succeeded,
                    "nested .lit import should use the imported file path as context:\n{}",
                    run_output
                );
                let module_manager = runtime.module_manager.borrow();
                assert!(module_manager.imported_modules.contains_key("Child"));
                assert!(module_manager.imported_modules.contains_key("Nested"));
                let child = module_manager.imported_modules.get("Child").unwrap();
                assert_eq!(child.import_dependencies, vec!["Nested".to_string()]);
            },
        );
    }

    #[test]
    fn cyclic_lit_file_import_is_rejected() {
        run_import_test_with_large_stack("cyclic_lit_file_import_is_rejected", || {
            let root = temp_test_dir("cyclic-lit-file-import");
            fs::write(
                root.join("A.lit"),
                "import \"./B.lit\" as B\nabstract_prop a_prop(x)",
            )
            .expect("write A .lit file");
            fs::write(
                root.join("B.lit"),
                "import \"./A.lit\" as A\nabstract_prop b_prop(x)",
            )
            .expect("write B .lit file");

            let source_code = format!("import \"{}\" as A", root.join("A.lit").to_string_lossy());
            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("repl");

            let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
            let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
                &runtime,
                &stmt_results,
                &runtime_error,
                false,
            );

            assert!(
                !run_succeeded,
                "cyclic .lit import should fail:\n{}",
                run_output
            );
            assert!(
                run_output.contains("cyclic import: A -> B -> A"),
                "cyclic .lit import should report the import chain:\n{}",
                run_output
            );
            let module_manager = runtime.module_manager.borrow();
            assert!(module_manager.imported_modules.is_empty());
            assert!(module_manager.loading_import_stack.is_empty());
        });
    }

    #[test]
    fn imported_prop_definition_can_verify_qualified_prop() {
        let path = write_temp_module(
            "prop-definition",
            r#"
prop imported_is_two(x Z):
    x = 2
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\n$Demo::imported_is_two(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("imported_prop_definition");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "imported prop definition should verify:\n{}",
            run_output
        );
    }

    #[test]
    fn imported_known_atomic_fact_can_verify_qualified_prop() {
        let path = write_temp_module(
            "known-atomic",
            r#"
abstract_prop imported_prop(x)
know $imported_prop(2)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\n$Demo::imported_prop(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("imported_known_atomic_fact");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "imported known atomic fact should verify:\n{}",
            run_output
        );
    }

    #[test]
    fn imported_local_citation_source_uses_module_relative_path() {
        let root = temp_test_dir("local-citation-source");
        let entry_path = root.join("entry.lit");
        let module_dir = root.join("module");
        fs::create_dir_all(&module_dir).expect("create temp module dir");
        fs::write(
            module_dir.join("main.lit"),
            r#"
abstract_prop imported_prop(x)
know $imported_prop(2)
"#,
        )
        .expect("write temp module");

        let source_code = "import \"module\" as Demo\n$Demo::imported_prop(2)";

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(entry_path.to_string_lossy().as_ref());
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "imported known atomic fact should verify:\n{}",
            run_output
        );
        assert!(run_output.contains("\"source_kind\": \"module\""));
        assert!(run_output.contains("\"source\": \"module\""));
        assert!(
            !run_output.contains(module_dir.to_string_lossy().as_ref()),
            "normal output should not expose the absolute module path:\n{}",
            run_output
        );
    }

    #[test]
    fn imported_std_citation_source_uses_std_module_label() {
        let source_code = "import Trig\n$Trig::periodic_with_period(Trig::sin, 2 * pi)";

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("imported_std_citation_source");
        let (stmt_results, runtime_error) = run_source_code(source_code, &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(run_succeeded, "std citation run failed:\n{}", run_output);
        assert!(
            run_output.contains("\"source_kind\": \"std\""),
            "std citation should include std source kind:\n{}",
            run_output
        );
        assert!(
            run_output.contains("\"source\": \"std/Trig\""),
            "std citation should include std module label:\n{}",
            run_output
        );
        assert!(
            !run_output.contains("\"path\""),
            "normal output should not expose the std source path:\n{}",
            run_output
        );
    }

    #[test]
    fn imported_known_forall_fact_can_verify_qualified_prop() {
        let path = write_temp_module(
            "known-forall",
            r#"
abstract_prop imported_prop(x)
know forall x Z:
    $imported_prop(x)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\n$Demo::imported_prop(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("imported_known_forall_fact");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "imported known forall fact should verify:\n{}",
            run_output
        );
    }

    #[test]
    fn imported_thm_can_be_cited_by_qualified_name() {
        let path = write_temp_module(
            "by-thm",
            r#"
abstract_prop imported_prop(x)

thm imported_thm:
    prove:
        forall x Z:
            $imported_prop(x)

    know $imported_prop(x)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nby thm Demo::imported_thm(2)\n$Demo::imported_prop(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("imported_thm_can_be_cited_by_qualified_name");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "qualified by-thm should cite imported module theorem:\n{}",
            run_output
        );
    }

    #[test]
    fn imported_module_proof_can_case_split_on_local_exist_witness() {
        let path = write_temp_module(
            "local-exist-case",
            r#"
know:
    forall n N:
        exist r N st {r = n}

thm local_exist_case:
    prove:
        forall n N:
            exist s N st {s = n}
    have by exist r N st {r = n}: r
    by cases:
        prove:
            exist s N st {s = n}
        case r < n + 1:
            witness exist s N st {s = n} from n:
                n = n
        case r >= n + 1:
            witness exist s N st {s = n} from n:
                n = n
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nby thm Demo::local_exist_case(2)\nexist s N st {{s = 2}}",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "imported_module_proof_can_case_split_on_local_exist_witness",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "imported module proof should keep local exist witnesses scoped:\n{}",
            run_output
        );
    }

    #[test]
    fn imported_strategy_can_be_enabled_by_qualified_name() {
        let path = write_temp_module(
            "by-strategy",
            r#"
abstract_prop imported_strategy_prop(x)

strategy imported_strategy:
    prove:
        forall x Z:
            x = 2
            =>:
                $imported_strategy_prop(x)

    know:
        forall y Z:
            y = 2
            =>:
                $imported_strategy_prop(y)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nuse strategy Demo::imported_strategy\n$Demo::imported_strategy_prop(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "imported_strategy_can_be_enabled_by_qualified_name",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "qualified by-strategy should enable imported module strategy:\n{}",
            run_output
        );
    }

    #[test]
    fn imported_strategy_can_be_stopped_by_qualified_name() {
        let path = write_temp_module(
            "stop-strategy",
            r#"
abstract_prop imported_strategy_prop(x)

strategy imported_strategy:
    prove:
        forall x Z:
            x = 2
            =>:
                $imported_strategy_prop(x)

    know:
        forall y Z:
            y = 2
            =>:
                $imported_strategy_prop(y)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nuse strategy Demo::imported_strategy\nstop strategy Demo::imported_strategy",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "imported_strategy_can_be_stopped_by_qualified_name",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "qualified stop-strategy should resolve and stop the imported module strategy:\n{}",
            run_output
        );

        let env = runtime
            .environment_stack
            .last()
            .expect("runtime should have a current environment");
        assert_eq!(
            env.used_strategy_stmts
                .get(&("Demo::imported_strategy_prop".to_string(), true)),
            Some(&"Demo::imported_strategy".to_string())
        );
        assert_eq!(
            env.stopped_strategy_stmts
                .get(&("Demo::imported_strategy_prop".to_string(), true)),
            Some(&"Demo::imported_strategy".to_string())
        );
    }

    #[test]
    fn stop_import_disables_imported_known_atomic_verification() {
        let path = write_temp_module(
            "stop-import-known-atomic",
            r#"
abstract_prop imported_prop(x)
know $imported_prop(2)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nstop import Demo\n$Demo::imported_prop(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "stop_import_disables_imported_known_atomic_verification",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            !run_succeeded,
            "stopped import should not verify by imported known atomic facts:\n{}",
            run_output
        );
        assert!(runtime
            .module_manager
            .borrow()
            .stopped_module
            .contains("Demo"));
    }

    #[test]
    fn stop_import_disables_imported_prop_definition_verification() {
        let path = write_temp_module(
            "stop-import-prop-definition",
            r#"
prop imported_is_two(x Z):
    x = 2
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nstop import Demo\n$Demo::imported_is_two(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "stop_import_disables_imported_prop_definition_verification",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            !run_succeeded,
            "stopped import should not verify by imported prop definitions:\n{}",
            run_output
        );
    }

    #[test]
    fn reimport_same_name_and_path_reactivates_stopped_import() {
        let path = write_temp_module(
            "reactivate-stopped-import",
            r#"
abstract_prop imported_prop(x)
know $imported_prop(2)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nstop import Demo\nimport \"{}\" as Demo\n$Demo::imported_prop(2)",
            path.to_string_lossy(),
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(
            "reimport_same_name_and_path_reactivates_stopped_import",
        );
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "same-name same-path reimport should reactivate the module:\n{}",
            run_output
        );
        assert!(!runtime
            .module_manager
            .borrow()
            .stopped_module
            .contains("Demo"));
    }

    #[test]
    fn clear_stops_imported_modules_until_reimported() {
        let path = write_temp_module(
            "clear-stops-import",
            r#"
abstract_prop imported_prop(x)
know $imported_prop(2)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nclear\n$Demo::imported_prop(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime
            .new_file_path_new_env_new_name_scope("clear_stops_imported_modules_until_reimported");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            !run_succeeded,
            "clear should stop existing imports for verification:\n{}",
            run_output
        );
        assert!(runtime
            .module_manager
            .borrow()
            .stopped_module
            .contains("Demo"));

        let source_code = format!(
            "import \"{}\" as Demo\nclear\nimport \"{}\" as Demo\n$Demo::imported_prop(2)",
            path.to_string_lossy(),
            path.to_string_lossy()
        );
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("clear_reimport_reactivates_module");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "reimport after clear should reactivate the module:\n{}",
            run_output
        );
    }

    #[test]
    fn by_thm_can_cite_stopped_imported_module() {
        let path = write_temp_module(
            "by-thm-after-stop-import",
            r#"
abstract_prop imported_prop(x)

thm imported_thm:
    prove:
        forall x Z:
            $imported_prop(x)

    know $imported_prop(x)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nstop import Demo\nby thm Demo::imported_thm(2)\n$Demo::imported_prop(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("by_thm_can_cite_stopped_imported_module");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "qualified by-thm should still cite a stopped imported module:\n{}",
            run_output
        );
    }

    #[test]
    fn use_strategy_can_cite_stopped_imported_module() {
        let path = write_temp_module(
            "by-strategy-after-stop-import",
            r#"
abstract_prop imported_strategy_prop(x)

strategy imported_strategy:
    prove:
        forall x Z:
            x = 2
            =>:
                $imported_strategy_prop(x)

    know:
        forall y Z:
            y = 2
            =>:
                $imported_strategy_prop(y)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nstop import Demo\nuse strategy Demo::imported_strategy\n$Demo::imported_strategy_prop(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime
            .new_file_path_new_env_new_name_scope("use_strategy_can_cite_stopped_imported_module");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "qualified by-strategy should still cite a stopped imported module:\n{}",
            run_output
        );
    }

    #[test]
    fn import_inside_prove_is_rejected() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code("prove:\n    import Trig", &mut runtime);

        assert!(runtime_error.is_some());
        assert!(runtime.module_manager.borrow().imported_modules.is_empty());
    }
}
