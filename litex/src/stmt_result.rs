use std::fmt;
use crate::stmt_success::StmtSuccess;
use crate::stmt_unknown::StmtUnknown;
use crate::errors::StmtError;

pub enum StmtResult<'a> {
    StmtSuccess(StmtSuccess<'a>),
    StmtUnknown(StmtUnknown<'a>),
    StmtError(StmtError),
}

impl<'a> fmt::Display for StmtResult<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StmtResult::StmtSuccess(stmt_success) => write!(f, "{}", stmt_success),
            StmtResult::StmtUnknown(stmt_unknown) => write!(f, "{}", stmt_unknown),
            StmtResult::StmtError(stmt_error) => write!(f, "{}", stmt_error),
        }
    }
}

