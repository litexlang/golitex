mod runtime_result;
mod runtime_success;
mod runtime_unknown;

pub use runtime_result::StmtResult;
pub(crate) use runtime_success::verified_by_from_stmt_result;
pub use runtime_success::{
    FactualStmtSuccess, NonFactualStmtSuccess, VerifiedByBuiltinRuleResult, VerifiedByFactResult,
    VerifiedByResult, VerifiedByVerifiedBysResult,
};
pub use runtime_unknown::StmtUnknown;
