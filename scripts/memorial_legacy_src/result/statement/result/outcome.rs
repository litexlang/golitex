//! Success-or-unknown outcome for one statement.

use crate::prelude::*;

/// The canonical result of executing one Litex statement.
///
#[derive(Debug)]
pub enum StmtResult {
    Success(SuccessStmtResult),
    Unknown(UnknownStmtResult),
}

/// Truth-proof phase output before the checked WD result is attached. This is
/// internal to fact verification and cannot be stored as a statement.
#[derive(Debug)]
pub enum ProveFactResult {
    Proven(Box<SuccessProveFactResult>),
    Unknown(UnknownStmtResult),
}

#[derive(Debug)]
pub enum UnknownStmtResult {
    Generic(Box<UnknownGenericStmtResult>),
    Fact(Box<UnknownFactResult>),
}
