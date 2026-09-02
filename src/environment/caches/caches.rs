//! Canonical Environment-scoped reusable verification caches.

use std::collections::HashMap;
/// Environment-scoped execution caches. Returned verification proofs never
/// live here; they are owned by the current verification process.
#[derive(Clone)]
pub struct EnvironmentVerificationCache {
    pub infer_rule_firings: HashMap<String, ()>,
}

impl EnvironmentVerificationCache {
    pub fn new() -> Self {
        Self {
            infer_rule_firings: HashMap::new(),
        }
    }
}
