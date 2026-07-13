use crate::pipeline::run_source_code;
use crate::prelude::*;
use std::fs;
use std::rc::Rc;

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

fn run_import_stmt(
    import_stmt: &ImportStmt,
    runtime: &mut Runtime,
    execution_mode: ExecutionMode,
) -> Result<StmtResult, RuntimeError> {
    let ImportStmt::ImportGlobalModule(stmt) = import_stmt;
    if runtime.run_mode == RunMode::Repository {
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
            return Ok(NonFactualStmtSuccess::new_with_stmt(import_stmt.clone().into()).into());
        }
    }
    Err(import_stmt_error(
        import_stmt,
        format!(
            "import `{}` is not a root module declared in litex.config; Litex no longer provides standard-library imports",
            stmt.mod_name
        ),
    ))
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

fn import_stmt_error(import_stmt: &ImportStmt, message: String) -> RuntimeError {
    let stmt: Stmt = import_stmt.clone().into();
    short_exec_error(stmt, message, None, vec![])
}

#[cfg(test)]
mod path_import_tests {
    use super::*;

    #[test]
    fn path_imports_do_not_resolve_as_modules() {
        for source in [
            "import \"./Demo\" as Demo",
            "trust import \"./Demo\" as Demo",
        ] {
            let mut runtime = Runtime::new_with_builtin_code();
            runtime.new_file_path_new_env_new_name_scope("repl");

            let (_, runtime_error) = run_source_code(source, &mut runtime);

            assert!(runtime_error.is_some(), "path import should fail");
            assert!(runtime.module_manager.module_by_name.is_empty());
        }
    }

    #[test]
    fn standard_library_imports_are_rejected() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code("import ZMod", &mut runtime);

        let runtime_error = runtime_error.expect("standard-library import should fail");
        assert!(format!("{:?}", runtime_error)
            .contains("Litex no longer provides standard-library imports"));
        assert!(runtime.module_manager.module_by_name.is_empty());
    }
}
