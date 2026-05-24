use crate::pipeline::run_source_code;
use crate::prelude::*;
use std::fs;
use std::path::{Path, PathBuf};

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
        Stmt::RunFileInStd(run_file_in_std) => {
            return run_file_in_std_folder(run_file_in_std, runtime);
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
    run_file_at_resolved_path(_run_file_stmt.clone().into(), path, _runtime)
}

fn run_file_in_std_folder(
    run_file_in_std: &RunFileInStd,
    runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    let path = resolve_run_file_in_std_path(run_file_in_std)?;
    run_file_at_resolved_path(run_file_in_std.clone().into(), path, runtime)
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

    let current_file_index = runtime.module_manager.current_file_index;
    runtime.new_file_and_update_runtime_with_file_content(path.as_str());

    let result = run_source_code(content.as_str(), runtime);

    runtime.change_file_index_to(current_file_index);

    if let Some(error) = result.1 {
        return Err(error);
    };

    return Ok((NonFactualStmtSuccess::new(stmt, InferResult::new(), result.0)).into());
}

fn resolve_run_file_in_std_path(run_file_in_std: &RunFileInStd) -> Result<String, RuntimeError> {
    let relative_main_lit_path = Path::new(run_file_in_std.file_path.as_str()).join("main.lit");
    let std_roots = candidate_std_roots();
    for std_root in std_roots.iter() {
        let candidate = std_root.join(&relative_main_lit_path);
        if candidate.is_file() {
            return Ok(candidate.to_string_lossy().into_owned());
        }
    }

    let attempted_paths = std_roots
        .iter()
        .map(|root| {
            root.join(&relative_main_lit_path)
                .to_string_lossy()
                .into_owned()
        })
        .collect::<Vec<_>>()
        .join(", ");
    let st: Stmt = run_file_in_std.clone().into();
    let lf = st.line_file();
    Err(RuntimeError::ExecStmtError(RuntimeErrorStruct::new(
        Some(st),
        format!(
            "Failed to find std run_file target `{}`. Tried: {}",
            run_file_in_std.file_path, attempted_paths
        ),
        lf,
        None,
        vec![],
    )))
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
    _import_stmt: &ImportStmt,
    _runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    unimplemented!();
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
}
