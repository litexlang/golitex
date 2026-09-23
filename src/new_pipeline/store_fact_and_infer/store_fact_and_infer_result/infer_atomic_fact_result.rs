use crate::new_pipeline::runtime::FactId;

use super::{InferAtomicExceptEqualityResult, InferEqualityResult};

// Same Equal / ExceptEquality split as verify's atomic result tree.
// Verify: first matching proof wins → store one result. Infer: every matching
// rule stores its derived facts → collect all hits in a Vec.
pub enum InferAtomicFactResult {
    EqualFact(Vec<InferEqualityResult>),
    ExceptEquality(Vec<InferAtomicExceptEqualityResult>),
}

impl InferAtomicFactResult {
    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        match self {
            Self::EqualFact(rules) => {
                let mut ids = Vec::new();
                for rule in rules {
                    ids.extend(rule.stored_fact_ids());
                }
                ids
            }
            Self::ExceptEquality(rules) => {
                let mut ids = Vec::new();
                for rule in rules {
                    ids.extend(rule.stored_fact_ids());
                }
                ids
            }
        }
    }
}
