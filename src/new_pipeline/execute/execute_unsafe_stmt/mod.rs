//! Explicit assumptions: `trust` and `trust have`.

mod exec_trust_have_stmt;
mod exec_trust_stmt;
mod exec_unsafe_stmt;

pub use exec_trust_have_stmt::{
    ExecTrustHaveStmtFailed, ExecTrustHaveStmtResult, ExecTrustHaveStmtSuccessResult,
};
pub use exec_trust_stmt::{ExecTrustStmtResult, ExecTrustStmtSuccessResult};
pub use exec_unsafe_stmt::ExecTrustBoundaryStmtResult;
