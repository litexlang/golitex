//! Successful fact storage and well-definedness outcomes.

use crate::prelude::*;

/// Successful output of executing one fact statement. Verification is a
/// recursive child result.
#[derive(Clone, Debug)]
pub struct SuccessStoreFactResult {
    /// Exact proposition whose store operation this node records.
    pub fact: Fact,
    /// Exact identity assigned when the source fact is stored. Proof-only
    /// child results deliberately retain `None`.
    pub fact_id: Option<FactId>,
    /// Ordered store/infer output produced after verification. This remains the
    /// existing `SuccessInferResult` payload during the infer-rule migration, but it
    /// is now owned by the store layer rather than the statement root.
    pub infers: SuccessInferResult,
}

#[derive(Debug, Default)]
pub struct SuccessVerifyFactWellDefinedResult {
    pub recursive: Option<Box<SuccessVerifyFactWellDefinedProofResult>>,
}

impl SuccessVerifyFactWellDefinedResult {
    pub fn new_recursive(recursive: SuccessVerifyFactWellDefinedProofResult) -> Self {
        Self {
            recursive: Some(Box::new(recursive)),
        }
    }
}

impl SuccessStoreFactResult {
    pub fn new(fact: Fact, infers: SuccessInferResult) -> Self {
        Self {
            fact,
            fact_id: None,
            infers,
        }
    }
}
