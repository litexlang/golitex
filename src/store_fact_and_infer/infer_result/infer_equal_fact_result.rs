use super::{
    InferEqualFactAdditiveCancellationResult, InferEqualFactCommonDenominatorCancellationResult,
    InferEqualFactNonzeroFactorCancellationResult,
    InferEqualFactNonzeroNumeratorCancellationResult, InferEqualFactPositiveRealPowerResult,
    InferEqualFactSubtractiveCancellationResult,
};
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub enum InferEqualFactResult {
    AdditiveCancellation(InferEqualFactAdditiveCancellationResult),
    NonzeroFactorCancellation(InferEqualFactNonzeroFactorCancellationResult),
    SubtractiveCancellation(InferEqualFactSubtractiveCancellationResult),
    CommonDenominatorCancellation(InferEqualFactCommonDenominatorCancellationResult),
    NonzeroNumeratorCancellation(InferEqualFactNonzeroNumeratorCancellationResult),
    PositiveRealPower(InferEqualFactPositiveRealPowerResult),
}

impl InferEqualFactResult {
    pub fn stored_conclusions(&self) -> Vec<&StoreInferredFactResult> {
        match self {
            Self::AdditiveCancellation(p) => vec![p.derived.as_ref()],
            Self::NonzeroFactorCancellation(p) => vec![p.derived.as_ref()],
            Self::SubtractiveCancellation(p) => vec![p.derived.as_ref()],
            Self::CommonDenominatorCancellation(p) => vec![p.derived.as_ref()],
            Self::NonzeroNumeratorCancellation(p) => vec![p.derived.as_ref()],
            Self::PositiveRealPower(p) => p.transports.iter().map(|t| &t.derived).collect(),
        }
    }

    pub fn stored_fact_ids(&self) -> Vec<FactId> {
        self.stored_conclusions()
            .into_iter()
            .flat_map(|s| s.stored_fact_ids())
            .collect()
    }
}
