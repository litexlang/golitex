use crate::prelude::*;
use std::fs;
use std::rc::Rc;

#[derive(Clone, Copy)]
enum RepositoryModuleRun {
    Complete,
    Before(RepositoryFileTarget),
    Through(RepositoryFileTarget),
}

impl RepositoryModuleRun {
    fn selected_target(self) -> Option<(RepositoryFileTarget, bool)> {
        match self {
            Self::Complete => None,
            Self::Before(target) => Some((target, false)),
            Self::Through(target) => Some((target, true)),
        }
    }
}

pub fn execute_repository_target(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    match target {
        RepositoryFileTarget::Module(module_id) => run_repository_module_prefix(runtime, module_id),
        RepositoryFileTarget::File { .. } => {
            run_repository_prefix(runtime, RepositoryModuleRun::Through(target))
        }
    }
}

pub fn run_repository_before_file_target(
    runtime: &mut Runtime,
    target: RepositoryFileTarget,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let RepositoryFileTarget::File { module_id, file_id } = target else {
        return (
            vec![],
            Some(repository_target_error(
                "a session -before target must be a registered project file",
            )),
        );
    };
    let file_exists = runtime
        .module_manager
        .module(module_id)
        .and_then(|module| module.file(file_id))
        .is_some();
    if !file_exists {
        return (
            vec![],
            Some(repository_target_error(
                "registered project file is missing",
            )),
        );
    }

    let execution_mode = runtime.current_execution_mode();
    let result = run_repository_prefix(runtime, RepositoryModuleRun::Before(target));
    if result.1.is_none() {
        runtime.push_file_execution_frame_with_mode(module_id, file_id, execution_mode);
        if let Err(error) = runtime.refresh_current_bare_symbol_index() {
            runtime.pop_execution_frame();
            return (result.0, Some(error));
        }
    }
    result
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
        let execution_mode = runtime.current_execution_mode();
        return run_repository_module_target_with_mode(runtime, root_module_id, execution_mode);
    }
    run_repository_prefix(
        runtime,
        RepositoryModuleRun::Through(RepositoryFileTarget::Module(target_module_id)),
    )
}

fn run_repository_prefix(
    runtime: &mut Runtime,
    module_run: RepositoryModuleRun,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let Some((target, _)) = module_run.selected_target() else {
        unreachable!("repository prefix requires a selected target")
    };
    let execution_mode = runtime.current_execution_mode();
    let target_module_id = match target {
        RepositoryFileTarget::Module(module_id) => module_id,
        RepositoryFileTarget::File { module_id, .. } => module_id,
    };
    let root_module_id = runtime
        .module_manager
        .entry_module_id
        .unwrap_or(target_module_id);
    if !runtime
        .module_manager
        .module_is_descendant_of(target_module_id, root_module_id)
    {
        return (
            vec![],
            Some(repository_target_error(
                "selected target is not inside the entry module export tree",
            )),
        );
    }
    run_repository_module_with_mode(runtime, root_module_id, execution_mode, module_run)
}

pub fn run_repository_module_target_with_mode(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    run_repository_module_with_mode(
        runtime,
        module_id,
        execution_mode,
        RepositoryModuleRun::Complete,
    )
}

fn run_repository_module_with_mode(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
    module_run: RepositoryModuleRun,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let Some(module) = runtime.module_manager.module(module_id) else {
        return (
            vec![],
            Some(repository_target_error(
                "registered project module is missing",
            )),
        );
    };
    if runtime.module_manager.entry_module_id == Some(module_id) {
        return run_repository_module_plan(runtime, module_id, execution_mode, module_run);
    }
    if module.status == ModuleStatus::Loaded {
        if matches!(module_run, RepositoryModuleRun::Complete)
            && execution_mode == ExecutionMode::Verified
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
        let message = if matches!(module_run, RepositoryModuleRun::Complete) {
            "cyclic module import while running project module"
        } else {
            "cyclic module import while running project prefix"
        };
        return (vec![], Some(repository_target_error(message)));
    }

    let module_manager_before = runtime.module_manager.clone();
    if let Err(message) = runtime
        .module_manager
        .begin_loading_discovered_module(module_id)
    {
        return (vec![], Some(repository_target_error(message.as_str())));
    }
    runtime
        .module_manager
        .module_mut(module_id)
        .expect("registered project module should exist")
        .execution_mode = execution_mode;
    let result = run_repository_module_plan(runtime, module_id, execution_mode, module_run);
    if result.1.is_some() {
        runtime.module_manager = module_manager_before;
        return result;
    }
    runtime.module_manager.finish_loading_module(module_id);
    result
}

fn run_repository_module_plan(
    runtime: &mut Runtime,
    module_id: ModuleId,
    execution_mode: ExecutionMode,
    module_run: RepositoryModuleRun,
) -> (Vec<StmtResult>, Option<RuntimeError>) {
    let (mut results, import_error) = run_config_imports(runtime, module_id);
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
    let source_path = module.main_file_path.clone();
    let module_source_file = module.module_source_file;
    if source_path.ends_with(".lit") {
        let Some(file_id) = module_source_file else {
            return (
                results,
                Some(repository_target_error(
                    "single-file module source is not registered",
                )),
            );
        };
        let (mut source_results, source_error) = run_repository_exported_file_target_with_mode(
            runtime,
            module_id,
            file_id,
            execution_mode,
        );
        results.append(&mut source_results);
        return (results, source_error);
    }

    let selected_target = module_run.selected_target();
    let run_targets = module.run_targets.clone();
    for target in run_targets {
        let (mut target_results, runtime_error, reached_selected_target) =
            if let Some((selected_target, include_selected_target)) = selected_target {
                let target_matches =
                    repository_target_matches_import_target(selected_target, target);
                if target_matches && !include_selected_target {
                    return (results, None);
                }
                let target_contains = match target {
                    ImportTarget::Module(child_module_id) => repository_target_is_inside_module(
                        runtime,
                        selected_target,
                        child_module_id,
                    ),
                    ImportTarget::File { .. } => false,
                };
                let target_execution_mode = if target_matches || target_contains {
                    execution_mode
                } else {
                    project_target_execution_mode(runtime, module_id, target)
                };
                let (target_results, runtime_error) = if target_contains && !target_matches {
                    let ImportTarget::Module(child_module_id) = target else {
                        unreachable!("only a module target can contain another project target")
                    };
                    run_repository_module_with_mode(
                        runtime,
                        child_module_id,
                        target_execution_mode,
                        module_run,
                    )
                } else {
                    run_repository_import_target(runtime, target, target_execution_mode)
                };
                (
                    target_results,
                    runtime_error,
                    target_matches || target_contains,
                )
            } else {
                let (target_results, runtime_error) =
                    run_repository_import_target(runtime, target, execution_mode);
                (target_results, runtime_error, false)
            };

        results.append(&mut target_results);
        if let Some(error) = runtime_error {
            return (results, Some(error));
        }
        if reached_selected_target {
            return (results, None);
        }
    }

    if selected_target.is_some() {
        (
            results,
            Some(repository_target_error(
                "selected target is missing from its recursive ordered [export] tree",
            )),
        )
    } else {
        (results, None)
    }
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
    runtime
        .module_manager
        .module_is_descendant_of(target_module_id, module_id)
}

fn run_config_imports(
    runtime: &mut Runtime,
    module_id: ModuleId,
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
        let import_execution_mode = config_import_execution_mode(runtime, &config_import);
        let (mut import_results, import_error) = run_repository_module_target_with_mode(
            runtime,
            config_import.module_id,
            import_execution_mode,
        );
        results.append(&mut import_results);
        if let Some(error) = import_error {
            return (results, Some(error));
        }
    }
    (results, None)
}

fn config_import_execution_mode(
    runtime: &mut Runtime,
    config_import: &ConfigImport,
) -> ExecutionMode {
    if runtime.run_options.strict_mode {
        return ExecutionMode::Verified;
    }
    let import_target = ImportTarget::Module(config_import.module_id);
    let name = runtime
        .module_manager
        .canonical_name_for_target(import_target)
        .unwrap_or("project import")
        .to_string();
    runtime.record_unverified_import("project_import", name, config_import.line_file.clone());
    ExecutionMode::Trusted
}

fn project_target_execution_mode(
    runtime: &mut Runtime,
    module_id: ModuleId,
    target: ImportTarget,
) -> ExecutionMode {
    if runtime.run_options.strict_mode {
        return ExecutionMode::Verified;
    }
    let line_file = runtime
        .module_manager
        .module(module_id)
        .and_then(|module| module.run_target_lines.get(&target))
        .cloned()
        .expect("every project run target should retain its config location");
    let name = runtime
        .module_manager
        .canonical_name_for_target(target)
        .unwrap_or("project export")
        .to_string();
    runtime.record_unverified_import("project_export", name, line_file);
    ExecutionMode::Trusted
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
    runtime.push_file_execution_frame_with_mode(module_id, file_id, execution_mode);
    if let Err(error) = runtime.refresh_current_bare_symbol_index() {
        runtime.pop_execution_frame();
        runtime.module_manager = module_manager_before;
        return (vec![], Some(error));
    }
    let result = run_repository_source_file(runtime, source_path.as_str());
    runtime.pop_execution_frame();
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
    let outcome =
        runtime.execute_source(remove_windows_carriage_from_str(source_code.as_str()).as_str());
    (outcome.stmt_results, outcome.runtime_error)
}

fn repository_target_error(message: &str) -> RuntimeError {
    ParseRuntimeError(RuntimeErrorStruct::new_with_msg_and_line_file(
        message.to_string(),
        (0, Rc::from("litex.config")),
    ))
    .into()
}
