//! Statement, source, and unknown-outcome inspection.

use crate::prelude::*;

impl StmtResult {
    pub fn statement(&self) -> Option<Stmt> {
        match self {
            StmtResult::Success(success) => Some(success.statement()),
            StmtResult::Unknown(_) => None,
        }
    }

    #[allow(dead_code)]
    pub fn line_file(&self) -> LineFile {
        match self {
            StmtResult::Success(success) => success.statement().line_file(),
            StmtResult::Unknown(UnknownStmtResult::Fact(unknown)) => unknown.goal().line_file(),
            StmtResult::Unknown(UnknownStmtResult::Generic(_)) => default_line_file(),
        }
    }

    pub fn is_success(&self) -> bool {
        !self.is_unknown()
    }

    pub fn is_unknown(&self) -> bool {
        matches!(self, StmtResult::Unknown(_))
    }

    pub fn as_unknown(&self) -> Option<&UnknownGenericStmtResult> {
        match self {
            StmtResult::Unknown(UnknownStmtResult::Generic(unknown)) => Some(unknown),
            _ => None,
        }
    }

    pub fn as_fact_unknown(&self) -> Option<&UnknownFactResult> {
        match self {
            StmtResult::Unknown(UnknownStmtResult::Fact(unknown)) => Some(unknown),
            _ => None,
        }
    }

    pub fn wrap_unknown_for_fact(self, fact: Fact) -> Self {
        match self {
            StmtResult::Unknown(UnknownStmtResult::Generic(unknown)) => {
                UnknownFactResult::from_stmt_unknown(fact, *unknown).into()
            }
            other => other,
        }
    }
}
