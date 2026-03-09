mod stmt_error;
mod stmt_result;
mod stmt_success;
mod stmt_unknown;

pub use stmt_result::{result_to_option_stmt_error, StmtResult};
pub use stmt_success::{FactVerifiedByBuiltinRules, FactVerifiedByFact, NonFactualStmtSuccess};
pub use stmt_unknown::StmtUnknown;
