use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferSetBuilderProjectionResult {
    BaseMembership(super::InferSetBuilderBaseMembershipResult),
    Condition {
        /// Zero-based index in the selected builder's original conditions.
        condition_index: usize,
        stored: StoreInferredFactResult,
    },
}

impl InferSetBuilderProjectionResult {
    pub fn stored(&self) -> &StoreInferredFactResult {
        match self {
            Self::BaseMembership(base) => &base.stored,
            Self::Condition { stored, .. } => stored,
        }
    }
    pub fn stored_mut(&mut self) -> &mut StoreInferredFactResult {
        match self {
            Self::BaseMembership(base) => &mut base.stored,
            Self::Condition { stored, .. } => stored,
        }
    }
}

impl From<super::InferSetBuilderBaseMembershipResult> for InferSetBuilderProjectionResult {
    fn from(result: super::InferSetBuilderBaseMembershipResult) -> Self {
        Self::BaseMembership(result)
    }
}
