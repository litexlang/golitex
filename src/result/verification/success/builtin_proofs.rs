//! Builtin fact proof outcomes.

use crate::prelude::*;

#[derive(Debug)]
pub struct SuccessBuiltinFactProofResult {
    pub msg: String,
    pub evidence: SuccessBuiltinFactProofEvidenceResult,
    pub subgoals: Vec<StmtResult>,
}

#[derive(Debug)]
pub enum SuccessBuiltinFactProofEvidenceResult {
    Typed(BuiltinRuleEvidence),
}

impl SuccessBuiltinFactProofEvidenceResult {
    pub fn typed(&self) -> Option<&BuiltinRuleEvidence> {
        match self {
            Self::Typed(evidence) => Some(evidence),
        }
    }

    pub fn typed_mut(&mut self) -> Option<&mut BuiltinRuleEvidence> {
        match self {
            Self::Typed(evidence) => Some(evidence),
        }
    }

    pub fn is_typed(&self) -> bool {
        true
    }
}
