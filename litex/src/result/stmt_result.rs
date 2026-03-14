use crate::common::keywords::SUCCESS;
use super::stmt_success::{FactVerifiedByBuiltinRules, FactVerifiedByFact, NonFactualStmtSuccess};
use super::stmt_unknown::StmtUnknown;

pub enum NonErrStmtResult {
    NonFactualStmtSuccess(NonFactualStmtSuccess),
    FactVerifiedByFact(FactVerifiedByFact),
    FactVerifiedByBuiltinRules(FactVerifiedByBuiltinRules),
    StmtUnknown(StmtUnknown),
}

const VERIFIED_BY: &str = "verified by:";

impl NonErrStmtResult {
    /// Returns the result body string without any line/file prefix (for tests or when location is not needed).
    pub fn body_string(&self) -> String {
        match self {
            NonErrStmtResult::NonFactualStmtSuccess(x) => format!("{}\n{}", SUCCESS, x.stmt),
            NonErrStmtResult::FactVerifiedByFact(x) => format!("{}\n{}\n{}\n{}", SUCCESS, x.fact, VERIFIED_BY, x.verified_by),
            NonErrStmtResult::FactVerifiedByBuiltinRules(x) => format!("{}\n{}\n{}\n{}", SUCCESS, x.fact, VERIFIED_BY, x.verified_by),
            NonErrStmtResult::StmtUnknown(x) => x.to_string(),
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