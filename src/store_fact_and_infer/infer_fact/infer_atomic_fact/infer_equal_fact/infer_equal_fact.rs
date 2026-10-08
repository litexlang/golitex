use crate::ast::fact::EqualFact;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferEqualityResult;

impl Runtime {
    // Collect every equality-infer rule that fires for a stored equal fact.
    // Cart equalities store ordinary set equality, without dimension facts.
    pub(crate) fn infer_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<Vec<InferEqualityResult>> {
        let mut rules = Vec::new();
        if let Some(pow) = self.infer_equal_fact_positive_real_power(equal_fact, verify_state)? {
            rules.push(InferEqualityResult::PositiveRealPower(pow));
        }
        Ok(rules)
    }
}
