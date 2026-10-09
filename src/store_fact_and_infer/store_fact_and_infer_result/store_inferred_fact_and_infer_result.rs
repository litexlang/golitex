use crate::execute::execute_fact_stmt::FactWellDefinedProof;

use super::StoreFactAndInferResult;

/// An inferred conclusion's actual formation check, followed by its store tree.
pub struct StoreInferredFactAndInferResult {
    pub well_defined: FactWellDefinedProof,
    pub store_and_infer: StoreFactAndInferResult,
}
