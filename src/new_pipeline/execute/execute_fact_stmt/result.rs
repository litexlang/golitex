use crate::new_pipeline::store_and_infer::StoreFactAndInferResult;

use super::verify_fact_result::VerifyFactResult;

// Pipeline: verify (how it ran) → store + infer (global env effect mirror).
// Local binder envs, if any, live on verify sub-nodes — not here.
pub struct ExecFactStmtResult {
    pub verify_result: VerifyFactResult,
    pub store_and_infer_result: StoreFactAndInferResult,
}