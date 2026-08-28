//! Success-or-unknown outcome for one statement.

use crate::prelude::*;

/// The canonical result of executing one Litex statement.
///
#[derive(Debug)]
pub enum StmtResult {
    Success(SuccessStmtResult),
    Unknown(UnknownStmtResult),
}

#[derive(Debug)]
pub enum UnknownStmtResult {
    Generic(Box<UnknownGenericStmtResult>),
    Fact(Box<UnknownFactResult>),
}
