use crate::pipeline::run_source_code;
use crate::prelude::*;
use std::fs;

pub fn run_stmt_at_global_env(
    stmt: &Stmt,
    runtime: &mut Runtime,
) -> Result<NonErrStmtExecResult, RuntimeError> {
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
) -> Result<NonErrStmtExecResult, RuntimeError> {
    let path = _run_file_stmt.file_path.as_str();
    let content = fs::read_to_string(path).map_err(|_| {
        RuntimeError::from(ExecStmtError::new_with_stmt(
            Stmt::RunFileStmt(_run_file_stmt.clone()),
            format!("Failed to read file: {}", path),
            None,
            vec![],
        ))
    })?;

    let current_file_index = _runtime.module_manager.current_file_index;
    _runtime.new_file_and_update_runtime_with_file_content(path);

    let result = run_source_code(content.as_str(), _runtime);

    _runtime.change_file_index_to(current_file_index);

    if let Some(error) = result.1 {
        return Err(error);
    };

    return Ok(NonErrStmtExecResult::NonFactualStmtSuccess(
        NonFactualStmtSuccess::new(
            Stmt::RunFileStmt(_run_file_stmt.clone()),
            InferResult::new(),
            result.0,
        ),
    ));
}

fn run_import_stmt(
    _import_stmt: &ImportStmt,
    _runtime: &mut Runtime,
) -> Result<NonErrStmtExecResult, RuntimeError> {
    unimplemented!();
}
