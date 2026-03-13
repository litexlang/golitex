use std::fmt;
use crate::common::keywords::{SUCCESS};
use super::stmt_success::{FactVerifiedByBuiltinRules, FactVerifiedByFact, NonFactualStmtSuccess};
use super::stmt_unknown::StmtUnknown;

pub enum NonErrStmtResult {
    NonFactualStmtSuccess(NonFactualStmtSuccess),
    FactVerifiedByFact(FactVerifiedByFact),
    FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules),
    StmtUnknown(StmtUnknown),
}

impl fmt::Display for NonErrStmtResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NonErrStmtResult::NonFactualStmtSuccess(x) => write!(f, "{}", x),
            NonErrStmtResult::FactVerifiedByFact(x) => write!(f, "{}", x),
            NonErrStmtResult::FactVerifiedByBuiltinRules(x) => write!(f, "{}\n{}", SUCCESS, x),
            NonErrStmtResult::StmtUnknown(x) => write!(f, "{}", x),
        }
    }
}

impl NonErrStmtResult {
    pub fn line_file(&self) -> Option<(usize, usize)> {
        match self {
            NonErrStmtResult::NonFactualStmtSuccess(x) => x.line_file_index,
            NonErrStmtResult::FactVerifiedByFact(x) => x.line_file_index,
            NonErrStmtResult::FactVerifiedByBuiltinRules(x) => x.line_file_index,
            NonErrStmtResult::StmtUnknown(_) => None,
        }
    }
}

// pub fn result_to_error<E>(result: Result<StmtResult, E>) -> Option<StmtError>
// where
//     E: Into<StmtError>,
// {
//     match result {
//         Err(e) => Some(e.into()),
//         Ok(StmtResult::StmtUnknown(_)) => {
//             Some(StmtError::UnknownError(UnknownError::new(UNKNOWN, None)))
//         }
//         Ok(_) => None,
//     }
// }

impl NonErrStmtResult {
    pub fn is_true(&self) -> bool {
        match self {
            NonErrStmtResult::NonFactualStmtSuccess(_) => true,
            NonErrStmtResult::FactVerifiedByFact(_) => true,
            NonErrStmtResult::FactVerifiedByBuiltinRules(_) => true,
            NonErrStmtResult::StmtUnknown(_) => false,
        }
    }
}