use super::{InferChainAdjacentResult, InferChainTransitiveClosureResult};

pub struct InferChainFactResult {
    pub adjacent_infers: Vec<InferChainAdjacentResult>,
    pub transitive_closures: Vec<InferChainTransitiveClosureResult>,
}
