//! Environment-scoped inference firing deduplication.

use std::collections::HashMap;
/// Persistent keys for inference rules already applied in this environment.
/// Returned verification proofs never live here; they are owned by the
/// current verification process.
#[derive(Clone)]
pub struct EnvironmentInferenceCache {
    pub infer_rule_firings: HashMap<String, ()>,
}

impl EnvironmentInferenceCache {
    pub fn new() -> Self {
        Self {
            infer_rule_firings: HashMap::new(),
        }
    }
}
