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
        Stmt::RunFileStmt(run_file_stmt) => {
            return run_file(run_file_stmt, runtime);
        }
        Stmt::ImportStmt(import_stmt) => {
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
    let current_lit_path = _runtime.module_manager.current_file_path_rc();
    let path = resolve_run_file_path(_run_file_stmt.file_path.as_str(), current_lit_path.as_ref());
    run_file_at_resolved_path(
        _run_file_stmt.clone().into(),
        path,
        Some(("run_file", "external_file")),
        _runtime,
    )
}

fn run_file_at_resolved_path(
    stmt: Stmt,
    path: String,
    display_source_label: Option<(&str, &str)>,
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

    let current_file_index = runtime.module_manager.current_file_index;
    if let Some((source_kind, source)) = display_source_label {
        runtime
            .module_manager
            .register_display_source_label(path.as_str(), source_kind, source);
    }
    runtime.new_file_and_update_runtime_with_file_content(path.as_str());

    let result = run_source_code(content.as_str(), runtime);

    runtime.change_file_index_to(current_file_index);

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
    let (module_name, absolute_path, is_std) = imported_module_info(import_stmt, runtime)?;
    runtime
        .module_manager
        .register_imported_module(module_name, absolute_path, is_std)
        .map_err(|msg| import_name_already_used_error(import_stmt, msg))?;

    Ok(NonFactualStmtSuccess::new_with_stmt(import_stmt.clone().into()).into())
}

fn imported_module_info(
    import_stmt: &ImportStmt,
    runtime: &Runtime,
) -> Result<(String, String, bool), RuntimeError> {
    match import_stmt {
        ImportStmt::ImportRelativePath(stmt) => {
            let module_name = import_module_name(
                stmt.as_mod_name.as_ref(),
                || module_name_from_path(&stmt.path, import_stmt),
                import_stmt,
            )?;
            let current_lit_path = runtime.module_manager.current_file_path_rc();
            let path = resolve_run_file_path(stmt.path.as_str(), current_lit_path.as_ref());
            Ok((
                module_name,
                absolute_path_string(PathBuf::from(path)),
                false,
            ))
        }
        ImportStmt::ImportGlobalModule(stmt) => {
            let module_name = import_module_name(
                stmt.as_mod_name.as_ref(),
                || Ok(stmt.mod_name.clone()),
                import_stmt,
            )?;
            Ok((module_name, std_import_path(stmt.mod_name.as_str()), true))
        }
    }
}

fn import_module_name<F>(
    as_mod_name: Option<&String>,
    default_name: F,
    import_stmt: &ImportStmt,
) -> Result<String, RuntimeError>
where
    F: FnOnce() -> Result<String, RuntimeError>,
{
    let name = match as_mod_name {
        Some(name) => name.clone(),
        None => default_name()?,
    };
    if let Err(msg) = is_valid_litex_name(name.as_str()) {
        return Err(import_stmt_error(
            import_stmt,
            format!("invalid import module name `{}`: {}", name, msg),
        ));
    }
    Ok(name)
}

fn module_name_from_path(path: &str, import_stmt: &ImportStmt) -> Result<String, RuntimeError> {
    match Path::new(path).file_stem() {
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

fn std_import_path(module_name: &str) -> String {
    let relative_main_lit_path = Path::new(module_name).join("main.lit");
    for std_root in candidate_std_roots() {
        let candidate = std_root.join(&relative_main_lit_path);
        if candidate.is_file() {
            return absolute_path_string(candidate);
        }
    }

    absolute_path_string(Path::new("std").join(relative_main_lit_path))
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
        let expected_path = entry_path
            .parent()
            .unwrap()
            .join("module")
            .join("main.lit")
            .to_string_lossy()
            .into_owned();

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(entry_path.to_string_lossy().as_ref());

        let (_, runtime_error) =
            run_source_code("import \"module/main.lit\" as demo", &mut runtime);

        assert!(runtime_error.is_none());
        let imported = runtime.module_manager.imported_modules.get("demo").unwrap();
        assert_eq!(imported.absolute_path, expected_path);
        assert!(!imported.is_std);
        assert!(imported.environment.defined_identifiers.is_empty());
        assert_eq!(
            runtime.module_manager.module_name_and_path_map.get("demo"),
            Some(&expected_path)
        );
    }

    #[test]
    fn import_std_module_registers_module_info() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code("import trigonometry as trig", &mut runtime);

        assert!(runtime_error.is_none());
        let imported = runtime.module_manager.imported_modules.get("trig").unwrap();
        assert!(imported.is_std);
        assert!(imported.absolute_path.contains("trigonometry"));
        assert_eq!(
            Path::new(imported.absolute_path.as_str())
                .file_name()
                .and_then(|name| name.to_str()),
            Some("main.lit")
        );
        assert_eq!(
            runtime.module_manager.module_name_and_path_map.get("trig"),
            Some(&imported.absolute_path)
        );
    }

    #[test]
    fn import_duplicate_module_name_is_rejected() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code(
            "import trigonometry as trig\nimport Nat as trig",
            &mut runtime,
        );

        let runtime_error = runtime_error.expect("duplicate module name should fail");
        match runtime_error {
            RuntimeError::NameAlreadyUsedError(error) => {
                assert!(error
                    .msg
                    .contains("module name `trig` has already been used"));
            }
            other => panic!("expected NameAlreadyUsedError, got {:?}", other),
        }
        assert_eq!(runtime.module_manager.imported_modules.len(), 1);
        let imported = runtime.module_manager.imported_modules.get("trig").unwrap();
        assert!(imported.absolute_path.contains("trigonometry"));
    }

    #[test]
    fn import_duplicate_module_path_is_rejected() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) = run_source_code(
            "import Nat as nat_alias\nimport Nat as other_nat",
            &mut runtime,
        );

        let runtime_error = runtime_error.expect("duplicate module path should fail");
        match runtime_error {
            RuntimeError::NameAlreadyUsedError(error) => {
                assert!(error
                    .msg
                    .contains("has already been imported as module name `nat_alias`"));
            }
            other => panic!("expected NameAlreadyUsedError, got {:?}", other),
        }
        assert_eq!(runtime.module_manager.imported_modules.len(), 1);
        assert!(runtime
            .module_manager
            .imported_modules
            .contains_key("nat_alias"));
    }

    #[test]
    fn import_equivalent_relative_paths_are_rejected() {
        let entry_path = std::env::temp_dir()
            .join("litex-import-entry")
            .join("entry.lit");

        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope(entry_path.to_string_lossy().as_ref());

        let (_, runtime_error) = run_source_code(
            "import \"module/main.lit\" as demo\nimport \"./module/main.lit\" as other_demo",
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
        assert_eq!(runtime.module_manager.imported_modules.len(), 1);
        assert!(runtime.module_manager.imported_modules.contains_key("demo"));
    }

    #[test]
    fn import_inside_prove_is_rejected() {
        let mut runtime = Runtime::new_with_builtin_code();
        runtime.new_file_path_new_env_new_name_scope("repl");

        let (_, runtime_error) =
            run_source_code("prove:\n    import trigonometry as trig", &mut runtime);

        assert!(runtime_error.is_some());
        assert!(runtime.module_manager.imported_modules.is_empty());
    }
}
