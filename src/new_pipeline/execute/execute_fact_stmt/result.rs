use super::verify_fact_result::VerifyFactResult2;
use crate::new_pipeline::runtime::FactId;

// Pipeline: verify (how it ran) → store + infer (global env effect mirror).
// Local binder envs, if any, live on verify sub-nodes — not here.
pub struct ExecFactStmtResult {
    pub verify_result: VerifyFactResult2,
    pub store_and_infer_result: StoreFactAndInferResult2,
}

// Mirror of what this fact wrote into the global ExecEnv (option A).
// Not a second store; ExecEnv remains authoritative.
pub struct StoreFactAndInferResult2 {
    pub stored_fact_ids: Vec<FactId>,
}

impl StoreFactAndInferResult2 {
    pub fn empty() -> Self {
        Self {
            stored_fact_ids: Vec::new(),
        }
    }
}
