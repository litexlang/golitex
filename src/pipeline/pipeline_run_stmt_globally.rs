use crate::pipeline::run_source_code;
use crate::prelude::*;
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::rc::Rc;

fn resolve_relative_path(user_path: &str, current_lit_file_path: &str) -> String {
    let user = Path::new(user_path);
    if user.is_absolute() {
        return user_path.to_string();
    }
    let current = Path::new(current_lit_file_path);
    let base_dir = current.parent().unwrap_or_else(|| Path::new(""));
    base_dir.join(user).to_string_lossy().into_owned()
}

fn trusted_import_not_allowed_in_strict_mode(stmt: Stmt) -> RuntimeError {
    short_exec_error(
        stmt,
        "strict mode does not allow trusted imports".to_string(),
        None,
        vec![],
    )
}

pub fn run_stmt_at_global_env(
    stmt: &Stmt,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    match stmt {
        Stmt::Command(CommandStmt::ImportStmt(import_stmt)) => {
            let execution_mode = runtime.current_execution_mode();
            let result = run_import_stmt(import_stmt, runtime, execution_mode);
            return runtime
                .finish_statement_execution(result, execution_mode == ExecutionMode::Trusted);
        }
        Stmt::Command(CommandStmt::TrustImportStmt(trust_import_stmt)) => {
            if runtime.strict_mode {
                return runtime.finish_statement_execution(
                    Err(trusted_import_not_allowed_in_strict_mode(stmt.clone())),
                    false,
                );
            }
            runtime.record_trusted_import(
                "trust_import",
                trust_import_stmt.import.to_string(),
                trust_import_stmt.line_file(),
            );
            let result =
                run_import_stmt(&trust_import_stmt.import, runtime, ExecutionMode::Trusted)
                    .map(|_| NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into());
            return runtime.finish_statement_execution(result, true);
        }
        Stmt::Command(CommandStmt::LocalImportStmt(local_import_stmt)) => {
            let execution_mode = runtime.current_execution_mode();
            let result = run_local_import_stmt(local_import_stmt, runtime, execution_mode);
            return runtime
                .finish_statement_execution(result, execution_mode == ExecutionMode::Trusted);
        }
        Stmt::Command(CommandStmt::TrustLocalImportStmt(trust_local_import_stmt)) => {
            if runtime.strict_mode {
                return runtime.finish_statement_execution(
                    Err(trusted_import_not_allowed_in_strict_mode(stmt.clone())),
                    false,
                );
            }
            runtime.record_trusted_import(
                "trust_local_import",
                trust_local_import_stmt.local_import.name.clone(),
                trust_local_import_stmt.line_file(),
            );
            let result = run_local_import_stmt(
                &trust_local_import_stmt.local_import,
                runtime,
                ExecutionMode::Trusted,
            )
            .map(|_| NonFactualStmtSuccess::new_with_stmt(stmt.clone()).into());
            return runtime.finish_statement_execution(result, true);
        }
        _ => {
            return runtime.exec_stmt(stmt);
        }
    }
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
    execution_mode: ExecutionMode,
) -> Result<StmtResult, RuntimeError> {
    if runtime.run_mode == RunMode::Repository {
        match import_stmt {
            ImportStmt::ImportRelativePath(_) => {
                return Err(import_stmt_error(
                    import_stmt,
                    "project mode import must name a root export or globally registered module; use litex.config and local import for module-local dependencies"
                        .to_string(),
                ));
            }
            ImportStmt::ImportGlobalModule(stmt) => {
                if let Some(target) = runtime.module_manager.root_export(&stmt.mod_name) {
                    let ImportTarget::Module(imported_module_id) = target else {
                        return Err(import_stmt_error(
                            import_stmt,
                            format!(
                                "root export `{}` is a file; files can only be loaded with local import inside their owner module",
                                stmt.mod_name
                            ),
                        ));
                    };
                    let importing_module_id = runtime.current_module_id();
                    load_discovered_module(
                        imported_module_id,
                        import_stmt.clone().into(),
                        runtime,
                        execution_mode,
                    )?;
                    runtime
                        .module_manager
                        .record_import_dependency(importing_module_id, imported_module_id);
                    return Ok(
                        NonFactualStmtSuccess::new_with_stmt(import_stmt.clone().into()).into(),
                    );
                }
            }
        }
    }

    let import_info = imported_module_info(import_stmt, runtime)?;
    let importing_module_id = runtime.current_module_id();
    let existing_module = runtime
        .module_manager
        .imported_module_can_be_loaded(&import_info.module_name, &import_info.module_root_path)
        .map_err(|msg| import_name_already_used_error(import_stmt, msg))?;
    if let Some(imported_module_id) = existing_module {
        let loaded_mode = runtime
            .module_manager
            .module(imported_module_id)
            .map(|module| module.execution_mode)
            .unwrap_or(ExecutionMode::Verified);
        if execution_mode == ExecutionMode::Verified && loaded_mode == ExecutionMode::Trusted {
            return Err(short_exec_error(
                import_stmt.clone().into(),
                "module was already loaded through trust import; restart the run before importing it normally"
                    .to_string(),
                None,
                vec![],
            ));
        }
        runtime
            .module_manager
            .record_import_dependency(importing_module_id, imported_module_id);
        return Ok(NonFactualStmtSuccess::new_with_stmt(import_stmt.clone().into()).into());
    }
    let module_manager_before_import = runtime.module_manager.clone();
    let parsing_free_params_before = runtime.parsing_free_param_collection.clone();
    let imported_module_id = runtime
        .module_manager
        .begin_loading_import(
            import_info.module_name.clone(),
            import_info.module_root_path.clone(),
            import_info.main_lit_path.clone(),
            import_info.is_std,
        )
        .map_err(|msg| import_stmt_error(import_stmt, msg))?;

    let content = fs::read_to_string(import_info.main_lit_path.as_str()).map_err(|_| {
        runtime.module_manager = module_manager_before_import.clone();
        import_stmt_error(
            import_stmt,
            format!(
                "Failed to read imported module entry file: {}",
                import_info.main_lit_path
            ),
        )
    })?;

    runtime
        .module_manager
        .module_mut(imported_module_id)
        .expect("imported module should exist")
        .execution_mode = execution_mode;
    runtime.parsing_free_param_collection = FreeParamCollection::new();
    runtime.push_module_execution_frame_with_mode(
        imported_module_id,
        import_info.main_lit_path.as_str(),
        execution_mode,
    );
    let (_stmt_results, runtime_error) = run_source_code(content.as_str(), runtime);
    runtime.pop_execution_frame();
    runtime.parsing_free_param_collection = parsing_free_params_before;
    if let Some(error) = runtime_error {
        runtime.module_manager = module_manager_before_import;
        return Err(short_exec_error(
            import_stmt.clone().into(),
            format!(
                "failed to import module `{}` from `{}`",
                import_info.module_name, import_info.module_root_path
            ),
            Some(error),
            vec![],
        ));
    }

    runtime
        .module_manager
        .finish_loading_import(imported_module_id);
    runtime
        .module_manager
        .record_import_dependency(importing_module_id, imported_module_id);

    Ok(NonFactualStmtSuccess::new_with_stmt(import_stmt.clone().into()).into())
}

fn run_local_import_stmt(
    local_import_stmt: &LocalImportStmt,
    runtime: &mut Runtime,
    execution_mode: ExecutionMode,
) -> Result<StmtResult, RuntimeError> {
    if runtime.run_mode != RunMode::Repository {
        return runtime.exec_local_import_stmt(local_import_stmt);
    }
    let module_id = runtime.current_module_id();
    let layer = runtime.current_layer();
    let target = runtime
        .module_manager
        .module(module_id)
        .and_then(|module| module.local_import_target(layer, &local_import_stmt.name))
        .ok_or_else(|| {
            short_exec_error(
                local_import_stmt.clone().into(),
                format!(
                    "local import `{}` was not declared for this source by its module's litex.config",
                    local_import_stmt.name
                ),
                None,
                vec![],
            )
        })?;

    match target {
        ImportTarget::File { module_id, file_id } => {
            load_exported_file(
                module_id,
                file_id,
                local_import_stmt.clone().into(),
                runtime,
                execution_mode,
            )?;
        }
        ImportTarget::Module(imported_module_id) => {
            load_discovered_module(
                imported_module_id,
                local_import_stmt.clone().into(),
                runtime,
                execution_mode,
            )?;
            runtime
                .module_manager
                .record_import_dependency(module_id, imported_module_id);
        }
    }
    runtime.activate_local_import(local_import_stmt.name.clone(), target);
    Ok(NonFactualStmtSuccess::new_with_stmt(local_import_stmt.clone().into()).into())
}

fn load_discovered_module(
    module_id: ModuleId,
    cause_stmt: Stmt,
    runtime: &mut Runtime,
    execution_mode: ExecutionMode,
) -> Result<(), RuntimeError> {
    let (status, loaded_mode) = runtime
        .module_manager
        .module(module_id)
        .map(|module| (module.status, module.execution_mode))
        .ok_or_else(|| {
            short_exec_error(
                cause_stmt.clone(),
                "discovered module is missing".to_string(),
                None,
                vec![],
            )
        })?;
    match status {
        ModuleStatus::Loaded => {
            if execution_mode == ExecutionMode::Verified && loaded_mode == ExecutionMode::Trusted {
                return Err(short_exec_error(
                    cause_stmt,
                    "module was already loaded through trust import; restart the run before importing it normally"
                        .to_string(),
                    None,
                    vec![],
                ));
            }
            return Ok(());
        }
        ModuleStatus::Loading => {
            let module_name = runtime
                .module_manager
                .module(module_id)
                .map(|module| module.module_name.clone())
                .unwrap_or_default();
            return Err(short_exec_error(
                cause_stmt,
                format!("cyclic module import involving `{}`", module_name),
                None,
                vec![],
            ));
        }
        ModuleStatus::Discovered => {}
    }

    let module_manager_before = runtime.module_manager.clone();
    let parsing_free_params_before = runtime.parsing_free_param_collection.clone();
    runtime
        .module_manager
        .begin_loading_discovered_module(module_id)
        .map_err(|message| short_exec_error(cause_stmt.clone(), message, None, vec![]))?;
    runtime
        .module_manager
        .module_mut(module_id)
        .expect("discovered module should exist")
        .execution_mode = execution_mode;
    let (module_name, main_lit_path) = {
        let module = runtime
            .module_manager
            .module(module_id)
            .expect("discovered module should exist");
        (module.module_name.clone(), module.main_file_path.clone())
    };

    let content = fs::read_to_string(&main_lit_path).map_err(|error| {
        runtime.module_manager = module_manager_before.clone();
        runtime.parsing_free_param_collection = parsing_free_params_before.clone();
        short_exec_error(
            cause_stmt.clone(),
            format!(
                "failed to read discovered module `{}` entry `{}`: {}",
                module_name, main_lit_path, error
            ),
            None,
            vec![],
        )
    })?;
    runtime.parsing_free_param_collection = FreeParamCollection::new();
    runtime.push_module_execution_frame_with_mode(module_id, &main_lit_path, execution_mode);
    let (_, runtime_error) = run_source_code(&content, runtime);
    runtime.pop_execution_frame();
    runtime.parsing_free_param_collection = parsing_free_params_before.clone();
    if let Some(error) = runtime_error {
        runtime.module_manager = module_manager_before;
        return Err(short_exec_error(
            cause_stmt,
            format!("failed to load discovered module `{}`", module_name),
            Some(error),
            vec![],
        ));
    }

    runtime.module_manager.finish_loading_import(module_id);
    Ok(())
}

fn load_exported_file(
    module_id: ModuleId,
    file_id: FileId,
    cause_stmt: Stmt,
    runtime: &mut Runtime,
    execution_mode: ExecutionMode,
) -> Result<(), RuntimeError> {
    let (status, source_path, canonical_name, loaded_mode) = runtime
        .module_manager
        .module(module_id)
        .and_then(|module| module.file(file_id))
        .map(|file| {
            (
                file.status,
                file.source_path.clone(),
                file.canonical_name.clone(),
                file.execution_mode,
            )
        })
        .ok_or_else(|| {
            short_exec_error(
                cause_stmt.clone(),
                "exported file is missing".to_string(),
                None,
                vec![],
            )
        })?;
    match status {
        FileStatus::Loaded => {
            if execution_mode == ExecutionMode::Verified && loaded_mode == ExecutionMode::Trusted {
                return Err(short_exec_error(
                    cause_stmt,
                    "file was already loaded through trust local import; restart the run before importing it normally"
                        .to_string(),
                    None,
                    vec![],
                ));
            }
            return Ok(());
        }
        FileStatus::Loading => {
            return Err(short_exec_error(
                cause_stmt,
                format!("cyclic local import involving `{}`", canonical_name),
                None,
                vec![],
            ));
        }
        FileStatus::Unloaded => {}
    }

    let module_manager_before = runtime.module_manager.clone();
    let parsing_free_params_before = runtime.parsing_free_param_collection.clone();
    runtime
        .module_manager
        .module_mut(module_id)
        .and_then(|module| module.file_mut(file_id))
        .expect("exported file should exist")
        .status = FileStatus::Loading;
    runtime
        .module_manager
        .module_mut(module_id)
        .and_then(|module| module.file_mut(file_id))
        .expect("exported file should exist")
        .execution_mode = execution_mode;
    let content = fs::read_to_string(&source_path).map_err(|error| {
        runtime.module_manager = module_manager_before.clone();
        short_exec_error(
            cause_stmt.clone(),
            format!("failed to read exported file `{}`: {}", source_path, error),
            None,
            vec![],
        )
    })?;
    runtime.parsing_free_param_collection = FreeParamCollection::new();
    runtime.push_file_execution_frame_with_mode(module_id, file_id, &source_path, execution_mode);
    let (_, runtime_error) = run_source_code(&content, runtime);
    runtime.pop_execution_frame();
    runtime.parsing_free_param_collection = parsing_free_params_before;
    if let Some(error) = runtime_error {
        runtime.module_manager = module_manager_before;
        return Err(short_exec_error(
            cause_stmt,
            format!("failed to load exported file `{}`", canonical_name),
            Some(error),
            vec![],
        ));
    }
    runtime
        .module_manager
        .module_mut(module_id)
        .and_then(|module| module.file_mut(file_id))
        .expect("exported file should exist")
        .status = FileStatus::Loaded;
    Ok(())
}

pub fn run_repository_file_target(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    match target {
        RepositoryFileTarget::Entrance(module_id) => {
            run_repository_entrance_target(runtime, module_id)
        }
        RepositoryFileTarget::File { module_id, file_id } => {
            run_repository_exported_file_target(runtime, module_id, file_id)
        }
    }
}

fn run_repository_entrance_target(
    runtime: &mut Runtime,
    module_id: ModuleId,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let Some(module) = runtime.module_manager.module(module_id) else {
        return (
            vec![],
            Some(repository_target_error("project entrance is missing")),
        );
    };
    let main_lit_path = module.main_file_path.clone();

    if runtime.current_module_id() == module_id {
        return run_repository_source_file(runtime, main_lit_path.as_str());
    }

    let module_manager_before = runtime.module_manager.clone();
    let parsing_free_params_before = runtime.parsing_free_param_collection.clone();
    if let Err(message) = runtime
        .module_manager
        .begin_loading_discovered_module(module_id)
    {
        return (vec![], Some(repository_target_error(message.as_str())));
    }
    runtime.parsing_free_param_collection = FreeParamCollection::new();
    runtime.push_module_execution_frame(module_id, main_lit_path.as_str());
    let result = run_repository_source_file(runtime, main_lit_path.as_str());
    runtime.pop_execution_frame();
    runtime.parsing_free_param_collection = parsing_free_params_before;
    if result.1.is_some() {
        runtime.module_manager = module_manager_before;
        return result;
    }
    runtime.module_manager.finish_loading_import(module_id);
    result
}

fn run_repository_exported_file_target(
    runtime: &mut Runtime,
    module_id: ModuleId,
    file_id: FileId,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let Some(file) = runtime
        .module_manager
        .module(module_id)
        .and_then(|module| module.file(file_id))
    else {
        return (
            vec![],
            Some(repository_target_error(
                "registered project file is missing",
            )),
        );
    };
    let source_path = file.source_path.clone();
    let status = file.status;
    if status == FileStatus::Loaded {
        return (vec![], None);
    }
    if status == FileStatus::Loading {
        return (
            vec![],
            Some(repository_target_error(
                "cyclic local import while running project file",
            )),
        );
    }

    let module_manager_before = runtime.module_manager.clone();
    let parsing_free_params_before = runtime.parsing_free_param_collection.clone();
    runtime
        .module_manager
        .module_mut(module_id)
        .and_then(|module| module.file_mut(file_id))
        .expect("registered project file should exist")
        .status = FileStatus::Loading;
    runtime.parsing_free_param_collection = FreeParamCollection::new();
    runtime.push_file_execution_frame(module_id, file_id, source_path.as_str());
    let result = run_repository_source_file(runtime, source_path.as_str());
    runtime.pop_execution_frame();
    runtime.parsing_free_param_collection = parsing_free_params_before;
    if result.1.is_some() {
        runtime.module_manager = module_manager_before;
        return result;
    }
    runtime
        .module_manager
        .module_mut(module_id)
        .and_then(|module| module.file_mut(file_id))
        .expect("registered project file should exist")
        .status = FileStatus::Loaded;
    result
}

fn run_repository_source_file(
    runtime: &mut Runtime,
    source_path: &str,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let source_code = match fs::read_to_string(source_path) {
        Ok(content) => content,
        Err(error) => {
            return (
                vec![],
                Some(
                    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
                        format!("failed to read project source `{}`: {}", source_path, error),
                        (0, Rc::from(source_path)),
                    ))
                    .into(),
                ),
            )
        }
    };
    run_source_code(
        remove_windows_carriage_return(source_code.as_str()).as_str(),
        runtime,
    )
}

fn repository_target_error(message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        (0, Rc::from("litex.config")),
    ))
    .into()
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
            let current_lit_path = runtime.current_file_path_rc();
            let path = resolve_relative_path(stmt.path.as_str(), current_lit_path.as_ref());
            let relative_entry = relative_import_entry(path.as_str(), import_stmt)?;
            let module_name = match stmt.as_mod_name.as_ref() {
                Some(name) => {
                    let module_name = validate_import_module_name(name.clone(), import_stmt)?;
                    validate_relative_import_alias_not_std_module(&module_name, import_stmt)?;
                    module_name
                }
                None => validate_import_module_name(
                    module_name_from_path(&stmt.path, import_stmt)?,
                    import_stmt,
                )?,
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
}

impl RelativeImportEntry {
    fn new(module_root_path: String, main_lit_path: String) -> Self {
        RelativeImportEntry {
            module_root_path,
            main_lit_path,
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
        return Err(import_stmt_error(
            import_stmt,
            "import cannot load a .lit file; declare it in [export] in litex.config and use `local import` inside that module"
                .to_string(),
        ));
    }

    validate_import_module_root(module_root, import_stmt)?;
    let main_lit_path = absolute_path_string(module_root.join("main.lit"));
    Ok(RelativeImportEntry::new(module_root_path, main_lit_path))
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
        let module_manager = &runtime.module_manager;
        let imported = module_manager.module_by_import_name("demo").unwrap();
        assert_eq!(imported.module_root_path, expected_path);
        assert!(!imported.is_std);
        assert!(imported
            .main_environment
            .defined_abstract_props
            .contains_key("loaded_prop"));
    }

    #[test]
    fn import_std_module_registers_module_info() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code("import Trig", &mut runtime);

        assert!(runtime_error.is_none());
        let module_manager = &runtime.module_manager;
        let imported = module_manager.module_by_import_name("Trig").unwrap();
        assert!(imported.is_std);
        assert!(imported.module_root_path.contains("Trig"));
        assert_eq!(
            Path::new(imported.module_root_path.as_str())
                .file_name()
                .and_then(|name| name.to_str()),
            Some("Trig")
        );
        assert!(imported
            .main_environment
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
        assert!(runtime.module_manager.module_by_name.is_empty());
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
        assert!(runtime.module_manager.module_by_name.is_empty());
    }

    #[test]
    fn import_std_module_without_as_uses_module_name() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code("import ZMod", &mut runtime);

        assert!(runtime_error.is_none());
        let module_manager = &runtime.module_manager;
        let imported = module_manager.module_by_import_name("ZMod").unwrap();
        assert!(imported.is_std);
        assert_eq!(
            Path::new(imported.module_root_path.as_str())
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
        let module_manager = &runtime.module_manager;
        assert_eq!(module_manager.module_by_name.len(), 1);
        assert!(module_manager.module_by_name.contains_key("Same"));
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
            "abstract_prop nested_prop(x)\ntrust $nested_prop(2)",
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
        let module_manager = &runtime.module_manager;
        assert!(module_manager.module_by_name.contains_key("Child"));
        assert!(module_manager.module_by_name.contains_key("Nested"));
        let child = module_manager.module_by_import_name("Child").unwrap();
        let nested_id = module_manager.module_id_by_name("Nested").unwrap();
        assert_eq!(child.imports, vec![nested_id]);
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
            "abstract_prop b_prop(x)\ntrust $b_prop(2)",
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
        let module_manager = &runtime.module_manager;
        assert_eq!(module_manager.module_by_name.len(), 2);
        assert!(module_manager.module_by_name.contains_key("A"));
        assert!(module_manager.module_by_name.contains_key("B"));
        let a = module_manager.module_by_import_name("A").unwrap();
        let b_id = module_manager.module_id_by_name("B").unwrap();
        assert_eq!(a.imports, vec![b_id]);
    }

    #[test]
    fn clear_keeps_cached_nested_imports_active() {
        let root = temp_test_dir("clear-keeps-cached-nested-imports-active");
        let nested_dir = root.join("Nested");
        let child_dir = root.join("Child");
        fs::create_dir_all(&nested_dir).expect("create nested module dir");
        fs::create_dir_all(&child_dir).expect("create child module dir");
        fs::write(
            nested_dir.join("main.lit"),
            "abstract_prop nested_prop(x)\ntrust $nested_prop(2)",
        )
        .expect("write nested module");
        fs::write(
            child_dir.join("main.lit"),
            "import \"../Nested\" as Nested\nabstract_prop child_prop(x)",
        )
        .expect("write child module");

        let source_code = format!(
            "import \"{}\" as Child\nclear\n$Nested::nested_prop(2)",
            child_dir.to_string_lossy()
        );
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("clear_keeps_cached_nested_imports_active");

        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "clear should leave Child and Nested active:\n{}",
            run_output
        );
        let module_manager = &runtime.module_manager;
        let child = module_manager.module_by_import_name("Child").unwrap();
        let nested_id = module_manager.module_id_by_name("Nested").unwrap();
        assert_eq!(child.imports, vec![nested_id]);
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
        assert!(runtime.module_manager.module_by_name.is_empty());
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
        let module_manager = &runtime.module_manager;
        assert!(module_manager.module_by_name.is_empty());
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
        let module_manager = &runtime.module_manager;
        assert!(module_manager.module_by_name.contains_key("Child"));
        assert!(module_manager.module_by_name.contains_key("Sibling"));
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
        let module_manager = &runtime.module_manager;
        assert_eq!(module_manager.module_by_name.len(), 1);
        let imported = module_manager.module_by_import_name("duplicate").unwrap();
        assert_eq!(
            imported.module_root_path,
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
        let module_manager = &runtime.module_manager;
        assert_eq!(module_manager.module_by_name.len(), 1);
        assert!(module_manager.module_by_name.contains_key("first_name"));
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
        let module_manager = &runtime.module_manager;
        assert_eq!(module_manager.module_by_name.len(), 1);
        assert!(module_manager.module_by_name.contains_key("demo"));
    }

    #[test]
    fn import_lit_file_path_is_rejected_even_with_alias() {
        run_import_test_with_large_stack(
            "import_lit_file_path_is_rejected_even_with_alias",
            || {
                let file_path = write_temp_lit_file(
                    "lit-file-path-registers-module",
                    "chap6_sketch.lit",
                    "abstract_prop loaded_prop(x)\ntrust $loaded_prop(2)",
                );
                let source_code = format!(
                    "import \"{}\" as chap6\n$chap6::loaded_prop(2)",
                    file_path.to_string_lossy()
                );

                let mut runtime = Runtime::new_with_builtin_code();
                runtime.new_file_path_new_env_new_name_scope(
                    "import_lit_file_path_registers_module_info",
                );
                let (stmt_results, runtime_error) =
                    run_source_code(source_code.as_str(), &mut runtime);
                let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
                    &runtime,
                    &stmt_results,
                    &runtime_error,
                    false,
                );

                assert!(!run_succeeded, "file import should fail:\n{}", run_output);
                assert!(
                    run_output.contains("import cannot load a .lit file"),
                    "file import should explain export file/local import:\n{}",
                    run_output
                );
                let module_manager = &runtime.module_manager;
                assert!(module_manager.module_by_import_name("chap6").is_none());
            },
        );
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
                output.contains("import cannot load a .lit file"),
                ".lit import without alias should report the file-import restriction, got: {}",
                output
            );
        });
    }

    #[test]
    fn rejected_lit_file_import_does_not_register_an_alias() {
        run_import_test_with_large_stack(
            "rejected_lit_file_import_does_not_register_an_alias",
            || {
                let root = temp_test_dir("equivalent-lit-file-paths");
                let entry_path = root.join("entry.lit");
                let file_path = root.join("module.lit");
                fs::write(&file_path, "abstract_prop loaded_prop(x)")
                    .expect("write temp .lit file");

                let mut runtime = Runtime::new_with_builtin_code();
                runtime.new_file_path_new_env_new_name_scope(entry_path.to_string_lossy().as_ref());

                let (_, runtime_error) = run_source_code(
                    "import \"module.lit\" as demo\nimport \"./module.lit\" as other_demo",
                    &mut runtime,
                );

                let runtime_error = runtime_error.expect(".lit import should fail");
                assert!(format!("{:?}", runtime_error).contains("import cannot load a .lit file"));
                let module_manager = &runtime.module_manager;
                assert!(module_manager.module_by_name.is_empty());
            },
        );
    }

    #[test]
    fn nested_lit_file_import_is_rejected_at_the_outer_import() {
        run_import_test_with_large_stack(
            "nested_lit_file_import_is_rejected_at_the_outer_import",
            || {
                let root = temp_test_dir("nested-lit-file-relative-path");
                let entry_path = root.join("entry.lit");
                let module_dir = root.join("module");
                fs::create_dir_all(&module_dir).expect("create temp module dir");
                fs::write(
                    module_dir.join("Nested.lit"),
                    "abstract_prop nested_prop(x)\ntrust $nested_prop(2)",
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
                    !run_succeeded,
                    "nested .lit import should fail:\n{}",
                    run_output
                );
                assert!(
                    run_output.contains("import cannot load a .lit file"),
                    "{run_output}"
                );
                let module_manager = &runtime.module_manager;
                assert!(module_manager.module_by_name.is_empty());
            },
        );
    }

    #[test]
    fn lit_file_import_is_rejected_before_cycle_loading() {
        run_import_test_with_large_stack(
            "lit_file_import_is_rejected_before_cycle_loading",
            || {
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

                let source_code =
                    format!("import \"{}\" as A", root.join("A.lit").to_string_lossy());
                let mut runtime = Runtime::new_with_builtin_code();
                runtime.new_file_path_new_env_new_name_scope("repl");

                let (stmt_results, runtime_error) =
                    run_source_code(source_code.as_str(), &mut runtime);
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
                    run_output.contains("import cannot load a .lit file"),
                    "{run_output}"
                );
                let module_manager = &runtime.module_manager;
                assert!(module_manager.module_by_name.is_empty());
                assert!(module_manager.loading_import_stack.is_empty());
            },
        );
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
trust $imported_prop(2)
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
trust $imported_prop(2)
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
trust forall x Z:
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
    ? forall x Z:
        $imported_prop(x)

    trust $imported_prop(x)
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
trust:
    forall n N:
        exist r N st {r = n}

thm local_exist_case:
    ? forall n N:
        exist s N st {s = n}
    obtain r from exist r N st {r = n}
    by cases:
        ? exist s N st {s = n}
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
    ? forall x Z:
        x = 2
        =>:
            $imported_strategy_prop(x)

    trust:
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
    ? forall x Z:
        x = 2
        =>:
            $imported_strategy_prop(x)

    trust:
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

        let env = &runtime.current_module().main_environment;
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
    fn clear_keeps_imported_modules_active() {
        let path = write_temp_module(
            "clear-keeps-import-active",
            r#"
abstract_prop imported_prop(x)
trust $imported_prop(2)
"#,
        );
        let source_code = format!(
            "import \"{}\" as Demo\nclear\n$Demo::imported_prop(2)",
            path.to_string_lossy()
        );

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("clear_keeps_imported_modules_active");
        let (stmt_results, runtime_error) = run_source_code(source_code.as_str(), &mut runtime);
        let (run_succeeded, run_output) = crate::pipeline::render_run_source_code_output(
            &runtime,
            &stmt_results,
            &runtime_error,
            false,
        );

        assert!(
            run_succeeded,
            "clear should leave existing imports active for verification:\n{}",
            run_output
        );
    }

    #[test]
    fn import_inside_question_goal_is_rejected() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) =
            run_source_code("claim:\n    ? 1 = 1\n    import Trig", &mut runtime);

        assert!(runtime_error.is_some());
        assert!(runtime.module_manager.module_by_name.is_empty());
    }
}
