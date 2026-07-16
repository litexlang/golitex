use crate::pipeline::run_source_code;
use crate::prelude::*;
use std::fs;
use std::rc::Rc;

pub fn run_stmt_at_global_env(
    stmt: &Stmt,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    match stmt {
        Stmt::Command(CommandStmt::ImportStmt(import)) => {
            let result = run_isolated_import(import, runtime);
            runtime.finish_statement_execution(result, false)
        }
        _ => runtime.exec_stmt(stmt),
    }
}

pub fn run_repository_file_target(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let isolated_before = runtime.isolated;
    runtime.isolated = false;
    let result = match target {
        RepositoryFileTarget::Module(module_id) => run_repository_module_prefix(runtime, module_id),
        RepositoryFileTarget::File { .. } => run_repository_prefix(runtime, target),
    };
    runtime.isolated = isolated_before;
    result
}

fn run_isolated_import(
    import: &ImportStmt,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    if !runtime.isolated {
        return Err(short_exec_error(
            import.clone().into(),
            "source import is only available in an isolated terminal".to_string(),
            None,
            vec![],
        ));
    }

    let module_manager_before = runtime.module_manager.clone();
    let discovery = match import {
        ImportStmt::Module(stmt) => discover_isolated_module_import(
            runtime,
            stmt.path.as_str(),
            stmt.alias.as_str(),
            stmt.line_file.clone(),
        ),
        ImportStmt::Std(stmt) => {
            discover_isolated_std_import(runtime, stmt.name.as_str(), stmt.line_file.clone())
        }
    };
    let module_id = match discovery {
        Ok(module_id) => module_id,
        Err(error) => {
            runtime.module_manager = module_manager_before;
            return Err(error);
        }
    };
    let isolated_before = runtime.isolated;
    runtime.isolated = false;
    let (_, runtime_error) = run_repository_module_target(runtime, module_id);
    runtime.isolated = isolated_before;
    if let Some(error) = runtime_error {
        runtime.module_manager = module_manager_before;
        return Err(error);
    }
    Ok(NonFactualStmtSuccess::new_with_stmt(import.clone().into()).into())
}

fn run_repository_module_prefix(
    runtime: &mut Runtime,
    target_module_id: ModuleId,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let root_module_id = runtime
        .module_manager
        .entry_module_id
        .unwrap_or(target_module_id);
    if root_module_id == target_module_id {
        return run_repository_module_target(runtime, root_module_id);
    }
    run_repository_prefix(runtime, RepositoryFileTarget::Module(target_module_id))
}

fn run_repository_prefix(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let execution_mode = runtime.current_execution_mode();
    let target_module_id = match target {
        RepositoryFileTarget::Module(module_id) => module_id,
        RepositoryFileTarget::File { module_id, .. } => module_id,
    };
    let root_module_id = runtime
        .module_manager
        .entry_module_id
        .unwrap_or(target_module_id);
    if !module_is_descendant_of(runtime, target_module_id, root_module_id) {
        return (
            vec![],
            Some(repository_target_error(
                "selected target is not inside the entry module export tree",
            )),
        );
    }
    run_repository_module_plan_to_target(runtime, root_module_id, execution_mode, target)
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
    let Some(module) = runtime.module_manager.module(module_id) else {
        return (
            vec![],
            Some(repository_target_error(
                "registered project module is missing",
            )),
        );
    };
    if runtime.current_module_id() == module_id {
        return run_repository_module_plan(runtime, module_id, execution_mode);
    }
    if module.status == ModuleStatus::Loaded {
        if execution_mode == ExecutionMode::Verified
            && module.execution_mode == ExecutionMode::Trusted
        {
            return (
                vec![],
                Some(repository_target_error(
                    "module was already loaded through a trusted configuration entry; restart the run before loading it normally",
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
    let result = run_repository_module_plan(runtime, module_id, execution_mode);
    runtime.pop_execution_frame();
    runtime.parsing_free_param_collection = parsing_free_params_before;
    if result.1.is_some() {
        runtime.module_manager = module_manager_before;
        return result;
    }
    runtime.module_manager.finish_loading_module(module_id);
    runtime
        .module_manager
        .module_mut(module_id)
        .expect("registered project module should exist")
        .strictly_verified = runtime.strict_mode && execution_mode == ExecutionMode::Verified;
    result
}

fn run_repository_module_prefix_with_mode(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
    target: RepositoryFileTarget,
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
        return run_repository_module_plan_to_target(runtime, module_id, execution_mode, target);
    }
    if module.status == ModuleStatus::Loaded {
        return (vec![], None);
    }
    if module.status == ModuleStatus::Loading {
        return (
            vec![],
            Some(repository_target_error(
                "cyclic module import while running project prefix",
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
    let result = run_repository_module_plan_to_target(runtime, module_id, execution_mode, target);
    runtime.pop_execution_frame();
    runtime.parsing_free_param_collection = parsing_free_params_before;
    if result.1.is_some() {
        runtime.module_manager = module_manager_before;
        return result;
    }
    runtime.module_manager.finish_loading_module(module_id);
    runtime
        .module_manager
        .module_mut(module_id)
        .expect("registered project module should exist")
        .strictly_verified = runtime.strict_mode && execution_mode == ExecutionMode::Verified;
    result
}

fn run_repository_module_plan_to_target(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
    selected_target: RepositoryFileTarget,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let (mut results, import_error) = run_config_imports(runtime, module_id, execution_mode);
    if let Some(error) = import_error {
        return (results, Some(error));
    }
    let Some(module) = runtime.module_manager.module(module_id) else {
        return (
            results,
            Some(repository_target_error(
                "registered project module is missing",
            )),
        );
    };
    let run_targets = module.run_targets.clone();
    for target in run_targets {
        let target_execution_mode =
            project_target_execution_mode(runtime, module_id, target, execution_mode);
        let target_matches = repository_target_matches_import_target(selected_target, target);
        let target_contains = match target {
            ImportTarget::Module(child_module_id) => {
                repository_target_is_inside_module(runtime, selected_target, child_module_id)
            }
            ImportTarget::File { .. } => false,
        };
        let (mut target_results, runtime_error) = if target_contains && !target_matches {
            let ImportTarget::Module(child_module_id) = target else {
                unreachable!("only a module target can contain another project target")
            };
            run_repository_module_prefix_with_mode(
                runtime,
                child_module_id,
                target_execution_mode,
                selected_target,
            )
        } else {
            run_repository_import_target(runtime, target, target_execution_mode)
        };
        results.append(&mut target_results);
        if let Some(error) = runtime_error {
            return (results, Some(error));
        }
        if target_matches || target_contains {
            return (results, None);
        }
    }
    (
        results,
        Some(repository_target_error(
            "selected target is missing from its recursive ordered [export] tree",
        )),
    )
}

fn run_repository_module_plan(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let (mut results, import_error) = run_config_imports(runtime, module_id, execution_mode);
    if let Some(error) = import_error {
        return (results, Some(error));
    }
    let Some(module) = runtime.module_manager.module(module_id) else {
        return (
            results,
            Some(repository_target_error(
                "registered project module is missing",
            )),
        );
    };
    let run_targets = module.run_targets.clone();
    for target in run_targets {
        let target_execution_mode =
            project_target_execution_mode(runtime, module_id, target, execution_mode);
        let (mut target_results, runtime_error) =
            run_repository_import_target(runtime, target, target_execution_mode);
        results.append(&mut target_results);
        if let Some(error) = runtime_error {
            return (results, Some(error));
        }
    }
    (results, None)
}

fn run_repository_import_target(
    runtime: &mut Runtime,
    target: ImportTarget,
    execution_mode: ExecutionMode,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    match target {
        ImportTarget::File { module_id, file_id } => run_repository_exported_file_target_with_mode(
            runtime,
            module_id,
            file_id,
            execution_mode,
        ),
        ImportTarget::Module(module_id) => {
            run_repository_module_target_with_mode(runtime, module_id, execution_mode)
        }
    }
}

fn repository_target_matches_import_target(
    target: RepositoryFileTarget,
    import_target: ImportTarget,
) -> bool {
    match (target, import_target) {
        (RepositoryFileTarget::Module(target_module), ImportTarget::Module(module_id)) => {
            target_module == module_id
        }
        (
            RepositoryFileTarget::File {
                module_id: target_module,
                file_id: target_file,
            },
            ImportTarget::File { module_id, file_id },
        ) => target_module == module_id && target_file == file_id,
        _ => false,
    }
}

fn repository_target_is_inside_module(
    runtime: &Runtime,
    target: RepositoryFileTarget,
    module_id: ModuleId,
) -> bool {
    let target_module_id = match target {
        RepositoryFileTarget::Module(target_module_id) => target_module_id,
        RepositoryFileTarget::File {
            module_id: target_module_id,
            ..
        } => target_module_id,
    };
    module_is_descendant_of(runtime, target_module_id, module_id)
}

fn module_is_descendant_of(
    runtime: &Runtime,
    module_id: ModuleId,
    ancestor_module_id: ModuleId,
) -> bool {
    let mut current_module_id = Some(module_id);
    while let Some(current) = current_module_id {
        if current == ancestor_module_id {
            return true;
        }
        current_module_id = runtime
            .module_manager
            .module(current)
            .and_then(|module| module.parent_module_id);
    }
    false
}

fn run_config_imports(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let Some(module) = runtime.module_manager.module(module_id) else {
        return (
            vec![],
            Some(repository_target_error(
                "registered project module is missing",
            )),
        );
    };
    let config_imports = module.config_imports.clone();
    let mut results = vec![];
    for config_import in config_imports {
        let import_target = ImportTarget::Module(config_import.module_id);
        let import_execution_mode = config_import_execution_mode(
            runtime,
            module_id,
            import_target,
            &config_import,
            execution_mode,
        );
        let (mut import_results, import_error) = run_repository_module_target_with_mode(
            runtime,
            config_import.module_id,
            import_execution_mode,
        );
        results.append(&mut import_results);
        if let Some(error) = import_error {
            return (results, Some(error));
        }
        runtime
            .module_manager
            .record_import_dependency(module_id, config_import.module_id);
    }
    (results, None)
}

fn config_import_execution_mode(
    runtime: &mut Runtime,
    owner_module_id: ModuleId,
    import_target: ImportTarget,
    config_import: &ConfigImport,
    inherited_mode: ExecutionMode,
) -> ExecutionMode {
    if inherited_mode == ExecutionMode::Trusted || runtime.strict_mode || !config_import.trusted {
        return inherited_mode;
    }
    if !project_target_is_loaded(runtime, import_target) {
        let name = runtime
            .module_manager
            .canonical_name_for_target(import_target)
            .unwrap_or("project import")
            .to_string();
        runtime.record_trusted_import(
            "trust_project_import",
            name,
            config_import.line_file.clone(),
        );
    }
    runtime
        .module_manager
        .record_import_dependency(owner_module_id, config_import.module_id);
    ExecutionMode::Trusted
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

#[cfg(test)]
mod path_import_tests {
    use super::*;

    #[test]
    fn fresh_runtime_has_no_preloaded_source_modules() {
        let runtime = Runtime::new();

        assert!(runtime.module_manager.modules.is_empty());
        assert!(runtime.module_manager.module_by_name.is_empty());
    }

    #[test]
    fn non_isolated_source_imports_require_the_terminal_boundary() {
        for source in ["import \"./Demo\" as Demo", "import std basics"] {
            let mut runtime = Runtime::new();
            runtime.new_file_path_new_env_new_name_scope("repl");

            let (_, runtime_error) = run_source_code(source, &mut runtime);

            let runtime_error = runtime_error.expect("non-isolated import should fail");
            assert!(format!("{runtime_error:?}").contains("only available in an isolated REPL"));
            assert!(runtime.module_manager.module_by_name.is_empty());
        }
    }

    #[test]
    fn trust_import_remains_removed() {
        let mut runtime = Runtime::new();
        runtime.isolated = true;
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code("trust import std basics", &mut runtime);

        let runtime_error = runtime_error.expect("trust import should fail");
        assert!(format!("{runtime_error:?}").contains("trust import has been removed"));
        assert!(runtime.module_manager.module_by_name.is_empty());
    }

    #[test]
    fn strict_mode_rejects_user_trust() {
        let mut runtime = Runtime::new();
        runtime.strict_mode = true;
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, trust_error) = run_source_code("trust 1 = 1", &mut runtime);
        assert!(trust_error.is_some(), "strict mode must reject user trust");
    }
}
