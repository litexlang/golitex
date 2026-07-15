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
                        "root export `{}` is a file; place it before this source in [export] instead of importing it",
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

    let module_name = runtime
        .module_manager
        .module(module_id)
        .map(|module| module.module_name.clone())
        .unwrap_or_default();
    let (_, runtime_error) =
        run_repository_module_target_with_mode(runtime, module_id, execution_mode);
    if let Some(error) = runtime_error {
        return Err(short_exec_error(
            cause_stmt,
            format!("failed to load discovered module `{}`", module_name),
            Some(error),
            vec![],
        ));
    }
    Ok(())
}

pub fn run_repository_file_target(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    match target {
        RepositoryFileTarget::Module(module_id) => run_repository_module_target(runtime, module_id),
        RepositoryFileTarget::File { module_id, file_id } => {
            run_repository_file_prefix(runtime, module_id, file_id)
        }
    }
}

fn run_repository_file_prefix(
    runtime: &mut Runtime,
    module_id: ModuleId,
    file_id: FileId,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let execution_mode = runtime.current_execution_mode();
    let root_module_id = runtime.module_manager.entry_module_id.unwrap_or(module_id);
    run_repository_module_plan_to_file(runtime, root_module_id, execution_mode, module_id, file_id)
}

fn run_repository_module_target(
    runtime: &mut Runtime,
    module_id: ModuleId,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let execution_mode = runtime.current_execution_mode();
    run_repository_module_target_with_mode(runtime, module_id, execution_mode)
}

fn run_repository_module_target_with_mode(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    run_repository_module_target_until_with_mode(runtime, module_id, execution_mode, None)
}

fn run_repository_module_target_until_with_mode(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
    last_target: Option<ImportTarget>,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let Some(module) = runtime.module_manager.module(module_id) else {
        return (
            vec![],
            Some(repository_target_error(
                "registered project module is missing",
            )),
        );
    };
    if runtime.current_module_id() == module_id {
        return run_repository_module_plan_until(runtime, module_id, execution_mode, last_target);
    }
    if module.status == ModuleStatus::Loaded {
        if execution_mode == ExecutionMode::Verified
            && module.execution_mode == ExecutionMode::Trusted
        {
            return (
                vec![],
                Some(repository_target_error(
                    "module was already loaded through trust import; restart the run before importing it normally",
                )),
            );
        }
        return (vec![], None);
    }
    if module.status == ModuleStatus::Loading {
        return (
            vec![],
            Some(repository_target_error(
                "cyclic module import while running project module",
            )),
        );
    }

    let module_manager_before = runtime.module_manager.clone();
    let parsing_free_params_before = runtime.parsing_free_param_collection.clone();
    if let Err(message) = runtime
        .module_manager
        .begin_loading_discovered_module(module_id)
    {
        return (vec![], Some(repository_target_error(message.as_str())));
    }
    let module_path = runtime
        .module_manager
        .module(module_id)
        .expect("registered project module should exist")
        .main_file_path
        .clone();
    runtime
        .module_manager
        .module_mut(module_id)
        .expect("registered project module should exist")
        .execution_mode = execution_mode;
    runtime.parsing_free_param_collection = FreeParamCollection::new();
    runtime.push_module_execution_frame_with_mode(module_id, module_path.as_str(), execution_mode);
    let result = run_repository_module_plan_until(runtime, module_id, execution_mode, last_target);
    runtime.pop_execution_frame();
    runtime.parsing_free_param_collection = parsing_free_params_before;
    if result.1.is_some() {
        runtime.module_manager = module_manager_before;
        return result;
    }
    runtime.module_manager.finish_loading_import(module_id);
    runtime
        .module_manager
        .module_mut(module_id)
        .expect("registered project module should exist")
        .strictly_verified = runtime.strict_mode && execution_mode == ExecutionMode::Verified;
    result
}

fn run_repository_module_plan_to_file(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
    target_module_id: ModuleId,
    target_file_id: FileId,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let Some(module) = runtime.module_manager.module(module_id) else {
        return (
            vec![],
            Some(repository_target_error(
                "registered project module is missing",
            )),
        );
    };
    let run_targets = module.run_targets.clone();
    let target_file = ImportTarget::File {
        module_id: target_module_id,
        file_id: target_file_id,
    };
    let mut results = vec![];
    for target in run_targets {
        let target_execution_mode =
            project_target_execution_mode(runtime, module_id, target, execution_mode);
        let (mut target_results, runtime_error) = if target == target_file {
            run_repository_exported_file_target_with_mode(
                runtime,
                target_module_id,
                target_file_id,
                target_execution_mode,
            )
        } else if let ImportTarget::Module(child_module_id) = target {
            if module_contains_file_target(
                runtime,
                child_module_id,
                target_module_id,
                target_file_id,
            ) {
                run_repository_module_target_until_with_mode(
                    runtime,
                    child_module_id,
                    target_execution_mode,
                    Some(target_file),
                )
            } else {
                run_repository_module_target_with_mode(
                    runtime,
                    child_module_id,
                    target_execution_mode,
                )
            }
        } else {
            let ImportTarget::File { module_id, file_id } = target else {
                unreachable!("project targets are files or modules");
            };
            run_repository_exported_file_target_with_mode(
                runtime,
                module_id,
                file_id,
                target_execution_mode,
            )
        };
        results.append(&mut target_results);
        if let Some(error) = runtime_error {
            return (results, Some(error));
        }
        if target == target_file
            || module_contains_file_target(
                runtime,
                match target {
                    ImportTarget::Module(child_module_id) => child_module_id,
                    ImportTarget::File { .. } => continue,
                },
                target_module_id,
                target_file_id,
            )
        {
            return (results, None);
        }
    }
    (
        results,
        Some(repository_target_error(
            "registered project file is missing from its ordered [export] plan",
        )),
    )
}

fn module_contains_file_target(
    runtime: &Runtime,
    module_id: ModuleId,
    target_module_id: ModuleId,
    target_file_id: FileId,
) -> bool {
    let Some(module) = runtime.module_manager.module(module_id) else {
        return false;
    };
    module.run_targets.iter().any(|target| match target {
        ImportTarget::File { module_id, file_id } => {
            *module_id == target_module_id && *file_id == target_file_id
        }
        ImportTarget::Module(child_module_id) => {
            module_contains_file_target(runtime, *child_module_id, target_module_id, target_file_id)
        }
    })
}

fn run_repository_module_plan_until(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
    last_target: Option<ImportTarget>,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let Some(module) = runtime.module_manager.module(module_id) else {
        return (
            vec![],
            Some(repository_target_error(
                "registered project module is missing",
            )),
        );
    };
    let run_targets = module.run_targets.clone();
    let mut results = vec![];
    for target in run_targets {
        let target_execution_mode =
            project_target_execution_mode(runtime, module_id, target, execution_mode);
        let (mut target_results, runtime_error) = match target {
            ImportTarget::File { module_id, file_id } => {
                run_repository_exported_file_target_with_mode(
                    runtime,
                    module_id,
                    file_id,
                    target_execution_mode,
                )
            }
            ImportTarget::Module(module_id) => {
                run_repository_module_target_with_mode(runtime, module_id, target_execution_mode)
            }
        };
        results.append(&mut target_results);
        if let Some(error) = runtime_error {
            return (results, Some(error));
        }
        if last_target == Some(target) {
            return (results, None);
        }
    }
    if last_target.is_some() {
        return (
            results,
            Some(repository_target_error(
                "registered project file is missing from its ordered [export] plan",
            )),
        );
    }
    (results, None)
}

fn project_target_execution_mode(
    runtime: &mut Runtime,
    module_id: ModuleId,
    target: ImportTarget,
    inherited_mode: ExecutionMode,
) -> ExecutionMode {
    if inherited_mode == ExecutionMode::Trusted || runtime.strict_mode {
        return inherited_mode;
    }
    let trusted_line = runtime
        .module_manager
        .module(module_id)
        .and_then(|module| module.trusted_run_targets.get(&target))
        .cloned();
    let Some(line_file) = trusted_line else {
        return ExecutionMode::Verified;
    };
    if !project_target_is_loaded(runtime, target) {
        let name = runtime
            .module_manager
            .canonical_name_for_target(target)
            .unwrap_or("project entry")
            .to_string();
        runtime.record_trusted_import("trust_project_export", name, line_file);
    }
    ExecutionMode::Trusted
}

fn project_target_is_loaded(runtime: &Runtime, target: ImportTarget) -> bool {
    match target {
        ImportTarget::File { module_id, file_id } => runtime
            .module_manager
            .module(module_id)
            .and_then(|module| module.file(file_id))
            .is_some_and(|file| file.status == FileStatus::Loaded),
        ImportTarget::Module(module_id) => runtime
            .module_manager
            .module(module_id)
            .is_some_and(|module| module.status == ModuleStatus::Loaded),
    }
}

fn run_repository_exported_file_target_with_mode(
    runtime: &mut Runtime,
    module_id: ModuleId,
    file_id: FileId,
    execution_mode: ExecutionMode,
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
                "cyclic project entry execution while running a project file",
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
    runtime
        .module_manager
        .module_mut(module_id)
        .and_then(|module| module.file_mut(file_id))
        .expect("registered project file should exist")
        .execution_mode = execution_mode;
    runtime.parsing_free_param_collection = FreeParamCollection::new();
    runtime.push_file_execution_frame_with_mode(
        module_id,
        file_id,
        source_path.as_str(),
        execution_mode,
    );
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
    runtime
        .module_manager
        .module_mut(module_id)
        .and_then(|module| module.file_mut(file_id))
        .expect("registered project file should exist")
        .strictly_verified = runtime.strict_mode && execution_mode == ExecutionMode::Verified;
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
