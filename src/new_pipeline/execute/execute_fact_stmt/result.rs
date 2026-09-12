use super::verify_fact_result::VerifyFactResult2;
use crate::new_pipeline::runtime::FactId;

// Fact statement exec result: proof track + global env effect mirror.
pub struct ExecFactStmtResult2 {
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
