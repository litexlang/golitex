use crate::pipeline::run_source_code;
use crate::prelude::*;
use std::fs;
use std::path::Path;

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
    let content = fs::read_to_string(path.as_str()).map_err(|_| {
        RuntimeError::ExecStmtError({
            let __stmt: Stmt = _run_file_stmt.clone().into();
            let __line_file = __stmt.line_file();
            RuntimeErrorStruct::new(
                Some(__stmt),
                format!("Failed to read file: {}", path.as_str()),
                __line_file,
                None,
                vec![],
            )
        })
    })?;

    let current_file_index = _runtime.module_manager.current_file_index;
    _runtime.new_file_and_update_runtime_with_file_content(path.as_str());

    let result = run_source_code(content.as_str(), _runtime);

    _runtime.change_file_index_to(current_file_index);

    if let Some(error) = result.1 {
        return Err(error);
    };

    return Ok((NonFactualStmtSuccess::new(
        _run_file_stmt.clone().into(),
        InferResult::new(),
        result.0,
    ))
    .into());
}

fn run_import_stmt(
    _import_stmt: &ImportStmt,
    _runtime: &mut Runtime,
) -> Result<StmtResult, RuntimeError> {
    unimplemented!();
}
