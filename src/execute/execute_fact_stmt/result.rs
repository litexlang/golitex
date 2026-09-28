use crate::store_fact_and_infer::StoreFactAndInferResult;

use super::verify_fact_result::VerifyFactResult;

// Pipeline: verify (how it ran) → store + infer (global env effect mirror).
// Local binder envs, if any, live on verify sub-nodes — not here.
pub struct ExecFactStmtSuccessResult {
    pub verify_result: VerifyFactResult,
    pub store_and_infer_result: StoreFactAndInferResult,
}

pub enum ExecFactStmtResult {
    Success(ExecFactStmtSuccessResult),
    Failed(VerifyFactResult),
}

impl ExecFactStmtResult {
    pub fn is_failed(&self) -> bool {
        matches!(self, Self::Failed(_))
    }
}
