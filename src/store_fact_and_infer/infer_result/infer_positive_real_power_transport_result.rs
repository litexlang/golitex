use super::InferPositiveRealPowerPositivityResult;
use crate::ast::obj::Obj;
use crate::execute::execute_fact_stmt::VerifyFactResult;
use crate::runtime::FactId;
use crate::store_fact_and_infer::StoreInferredFactResult;

pub struct InferPositiveRealPowerTransportResult {
    pub source_fact_id: FactId,
    pub power: Obj,
    pub positivity: InferPositiveRealPowerPositivityResult,
    pub exponent_real: VerifyFactResult,
    pub derived: StoreInferredFactResult,
}
