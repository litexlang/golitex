use super::InferNotExistDemorganForallResult;

pub enum InferNotExistFactResult {
    // Rule: `not exist` exposes De Morgan forall when body shape is supported.
    DemorganForall(InferNotExistDemorganForallResult),
    NoInfer,
}
