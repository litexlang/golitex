//! Successful trusted and unsafe statement outcomes.

use crate::prelude::*;

pub struct SuccessTrustStmtResult {
    pub statement: TrustStmt,
    pub common: SuccessStmtCommonResult,
}

pub struct SuccessTrustHaveStmtResult {
    pub statement: TrustHaveStmt,
    pub common: SuccessStmtCommonResult,
}

pub enum SuccessUnsafeStmtResult {
    TrustStmt(Box<SuccessTrustStmtResult>),
    TrustHaveStmt(Box<SuccessTrustHaveStmtResult>),
}
