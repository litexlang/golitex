use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferEqualFactNonzeroNumeratorCancellationResult {
    pub source_fact_id: FactId,
    pub common_operand: Obj,
    pub left_in_c_proof: VerifyFactResult,
    pub right_in_c_proof: VerifyFactResult,
    pub common_in_c_proof: VerifyFactResult,
    pub numerator_nonzero_proof: VerifyFactResult,
    pub left_denominator_nonzero_proof: VerifyFactResult,
    pub right_denominator_nonzero_proof: VerifyFactResult,
    pub derived: Box<StoreInferredFactResult>,
}

impl InferEqualFactNonzeroNumeratorCancellationResult {
    pub fn new(
        source_fact_id: FactId,
        common_operand: Obj,
        left_in_c_proof: VerifyFactResult,
        right_in_c_proof: VerifyFactResult,
        common_in_c_proof: VerifyFactResult,
        numerator_nonzero_proof: VerifyFactResult,
        left_denominator_nonzero_proof: VerifyFactResult,
        right_denominator_nonzero_proof: VerifyFactResult,
        derived: StoreInferredFactResult,
    ) -> Self {
        Self {
            source_fact_id,
            common_operand,
            left_in_c_proof,
            right_in_c_proof,
            common_in_c_proof,
            numerator_nonzero_proof,
            left_denominator_nonzero_proof,
            right_denominator_nonzero_proof,
            derived: Box::new(derived),
        }
    }
}
