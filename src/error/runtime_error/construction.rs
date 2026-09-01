//! Runtime error and payload construction helpers.

use super::{RuntimeError, RuntimeErrorOutput, RuntimeErrorStruct};
use crate::prelude::*;

impl RuntimeErrorStruct {
    pub fn new(
        statement: Option<Stmt>,
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<StmtResult>,
    ) -> Self {
        RuntimeErrorStruct {
            statement,
            msg,
            line_file,
            previous_error: previous_error.map(Box::new),
            inside_results,
            output: Box::new(RuntimeErrorOutput::new()),
        }
    }

    pub fn new_with_output(
        statement: Option<Stmt>,
        msg: String,
        line_file: LineFile,
        previous_error: Option<RuntimeError>,
        inside_results: Vec<StmtResult>,
        output: RuntimeErrorOutput,
    ) -> Self {
        RuntimeErrorStruct {
            statement,
            msg,
            line_file,
            previous_error: previous_error.map(Box::new),
            inside_results,
            output: Box::new(output),
        }
    }
}

pub fn short_exec_error(
    stmt: Stmt,
    message: impl Into<String>,
    cause: Option<RuntimeError>,
    inside_results: Vec<StmtResult>,
) -> RuntimeError {
    let message = message.into();
    let line_file = stmt.line_file();
    RuntimeError::ExecStmtError(Box::new(RuntimeErrorStruct::new(
        Some(stmt.clone()),
        message,
        line_file.clone(),
        cause,
        inside_results,
    )))
}

pub fn exec_stmt_error_with_stmt_and_cause(stmt: Stmt, cause: RuntimeError) -> RuntimeError {
    RuntimeError::ExecStmtError(Box::new(RuntimeErrorStruct::new(
        Some(stmt.clone()),
        String::new(),
        stmt.line_file(),
        Some(cause),
        vec![],
    )))
}

impl RuntimeErrorStruct {
    pub fn new_with_just_msg(msg: String) -> Self {
        Self::new(None, msg, default_line_file(), None, vec![])
    }

    pub fn new_with_msg_and_line_file(msg: String, line_file: LineFile) -> Self {
        Self::new(None, msg, line_file, None, vec![])
    }

    pub fn new_with_msg_and_cause(msg: String, cause: RuntimeError) -> Self {
        Self::new(None, msg, default_line_file(), Some(cause), vec![])
    }
}
