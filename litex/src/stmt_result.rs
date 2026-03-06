use std::fmt;
use crate::stmt_success::StmtSuccess;
use crate::stmt_unknown::StmtUnknown;
use crate::errors::StmtError;

pub enum StmtResult {
    StmtSuccess(StmtSuccess),
    StmtUnknown(StmtUnknown),
    StmtError(StmtError, Option<(usize, usize)>),
}

impl fmt::Display for StmtResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StmtResult::StmtSuccess(stmt_success) => write!(f, "{}", stmt_success),
            StmtResult::StmtUnknown(stmt_unknown) => write!(f, "{}", stmt_unknown),
            StmtResult::StmtError(stmt_error, line_file_index) => {
                if let Some((line, file_index)) = line_file_index {
                    write!(f, "line {}, file index {}\n{}", line, file_index, stmt_error)
                } else {
                    write!(f, "{}", stmt_error)
                }
            }
        }
    }
}

