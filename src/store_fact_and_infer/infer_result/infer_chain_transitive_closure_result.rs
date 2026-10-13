use super::ChainTransitiveCite;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferChainTransitiveClosureResult {
    pub cite: ChainTransitiveCite,
    pub start_object_index: usize,
    pub end_object_index: usize,
    pub premise_edge_indexes: Vec<usize>,
    pub derived: Box<StoreInferredFactResult>,
}
