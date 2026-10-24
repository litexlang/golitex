use crate::execute::execute_fact_stmt::function_signature_selection::FunctionSignatureSelection;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferInFactFnRangeResult {
    pub signature_selection: FunctionSignatureSelection,
    pub codomain_membership: StoreInferredFactResult,
    pub preimage_witness: Option<StoreInferredFactResult>,
}
