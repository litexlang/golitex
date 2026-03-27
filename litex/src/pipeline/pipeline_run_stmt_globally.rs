use crate::error::RuntimeError;
use crate::result::NonErrStmtExecResult;
use crate::runtime::Runtime;
use crate::stmt::tooling_stmt::ImportStmt;
use crate::stmt::tooling_stmt::RunFileStmt;
use crate::stmt::Stmt;

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
    unimplemented!();
}

fn run_import_stmt(
    _import_stmt: &ImportStmt,
    _runtime: &mut Runtime,
) -> Result<NonErrStmtExecResult, RuntimeError> {
    unimplemented!();
}
