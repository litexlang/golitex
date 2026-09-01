//! Inference result shared by successful non-factual statements.

use crate::prelude::*;

/// Execution evidence shared by every successful non-factual statement.
/// Recursive verification children belong to the statement-specific result,
/// never to this common execution envelope.
#[derive(Debug)]
pub struct SuccessStmtCommonResult {
    pub infers: SuccessInferResult,
}

impl SuccessStmtCommonResult {
    pub fn new(infers: SuccessInferResult) -> Self {
        Self { infers }
    }
}
