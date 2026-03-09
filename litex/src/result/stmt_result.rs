use std::fmt;
use crate::error::StmtError;
use crate::common::keywords::SUCCESS;
use super::stmt_success::{FactVerifiedByBuiltinRules, FactVerifiedByFact, NonFactualStmtSuccess};
use super::stmt_unknown::StmtUnknown;

pub enum StmtResult {
    NonFactualStmtSuccess(NonFactualStmtSuccess),
    FactVerifiedByFact(FactVerifiedByFact),
    FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules),
    StmtUnknown(StmtUnknown),
    StmtError(StmtError),
}

impl fmt::Display for StmtResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StmtResult::NonFactualStmtSuccess(x) => write!(f, "{}", x),
            StmtResult::FactVerifiedByFact(x) => write!(f, "{}", x),
            StmtResult::FactVerifiedByBuiltinRules(x) => write!(f, "{}\n{}", SUCCESS, x),
            StmtResult::StmtUnknown(x) => write!(f, "{}", x),
            StmtResult::StmtError(x) => write!(f, "{}", x),
        }
    }
}

impl StmtResult {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            StmtResult::NonFactualStmtSuccess(x) => x.line_file_index,
            StmtResult::FactVerifiedByFact(x) => x.line_file_index,
            StmtResult::FactVerifiedByBuiltinRules(x) => x.line_file_index,
            StmtResult::StmtUnknown(_) => None,
            StmtResult::StmtError(x) => x.line_file(),
        }
    }
}
