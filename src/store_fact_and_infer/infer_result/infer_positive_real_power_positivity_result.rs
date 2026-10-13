use crate::execute::execute_fact_stmt::VerifyFactResult;

pub enum InferPositiveRealPowerPositivityResult {
    PowerPositive(VerifyFactResult),
    BasePositive(VerifyFactResult),
}
