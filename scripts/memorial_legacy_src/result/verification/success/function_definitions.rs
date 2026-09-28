//! Function definition verification outcomes.

use crate::prelude::*;

#[derive(Debug)]
pub struct SuccessVerifyFunctionDefinitionResult {
    pub return_check: Box<VerifyFactResult>,
    /// Membership/domain facts installed while checking the return value,
    /// with their temporary FactIds frozen before that local scope closes.
    pub assumption_infers: SuccessInferResult,
    pub function_membership: Fact,
    pub defining_equality: Fact,
}

impl SuccessVerifyFunctionDefinitionResult {
    pub fn new(
        return_check: VerifyFactResult,
        assumption_infers: SuccessInferResult,
        function_membership: Fact,
        defining_equality: Fact,
    ) -> Self {
        Self {
            return_check: Box::new(return_check),
            assumption_infers,
            function_membership,
            defining_equality,
        }
    }
}
