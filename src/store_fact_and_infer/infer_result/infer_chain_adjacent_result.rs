use super::InferAtomicFactResult;
use crate::ast::fact::Fact;

pub struct InferChainAdjacentResult {
    pub edge_index: usize,
    pub fact: Fact,
    pub infer: InferAtomicFactResult,
}

impl InferChainAdjacentResult {
    pub fn new(edge_index: usize, fact: Fact, infer: InferAtomicFactResult) -> Self {
        Self {
            edge_index,
            fact,
            infer,
        }
    }
}
