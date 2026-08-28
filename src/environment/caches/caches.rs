//! Canonical Environment-scoped reusable verification caches.

use crate::prelude::*;
use std::collections::HashMap;

/// Environment-scoped verification results reusable by later statements.
#[derive(Clone)]
pub struct EnvironmentVerificationCache {
    pub well_defined_objects: HashMap<WellDefinedCacheKey, CachedWellDefinedObj>,
    pub infer_rule_firings: HashMap<String, ()>,
}

impl EnvironmentVerificationCache {
    pub fn new() -> Self {
        Self {
            well_defined_objects: HashMap::new(),
            infer_rule_firings: HashMap::new(),
        }
    }
}
