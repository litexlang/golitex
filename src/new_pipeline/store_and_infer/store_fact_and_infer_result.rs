use crate::new_pipeline::runtime::FactId;

// Mirror of what this fact wrote into the global ExecEnv.
// Not a second store; ExecEnv remains authoritative.
pub struct StoreFactAndInferResult {
    pub stored_fact_ids: Vec<FactId>,
}

impl StoreFactAndInferResult {
    pub fn empty() -> Self {
        Self {
            stored_fact_ids: Vec::new(),
        }
    }

    pub fn from_stored_ids(stored_fact_ids: Vec<FactId>) -> Self {
        Self { stored_fact_ids }
    }
}

// Placeholder until infer rules are wired.
pub struct InferFromStoredFactResult {
    pub _wire: (),
}

impl InferFromStoredFactResult {
    pub fn empty() -> Self {
        Self { _wire: () }
    }
}
