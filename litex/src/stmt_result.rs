use std::fmt;
use crate::stmt_success::StmtSuccess;
use crate::stmt_unknown::StmtUnknown;
use crate::errors::StmtError;

pub enum StmtResult {
    StmtSuccess(StmtSuccess),
    StmtUnknown(StmtUnknown),
    StmtError(StmtError),
}

impl fmt::Display for StmtResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StmtResult::StmtSuccess(stmt_success) => write!(f, "{}", stmt_success),
            StmtResult::StmtUnknown(stmt_unknown) => write!(f, "{}", stmt_unknown),
            StmtResult::StmtError(stmt_error) => {
                write!(f, "{}", stmt_error)
            }
        }
    }
}


impl StmtResult {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            StmtResult::StmtSuccess(stmt_success) => stmt_success.line_file(),
            StmtResult::StmtUnknown(stmt_unknown) => stmt_unknown.line_file_index,
            StmtResult::StmtError(stmt_error) => stmt_error.line_file(),
        }
    }
}