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
        rules.extend(self.infer_equal_fact_additive_cancellation(equal_fact, verify_state)?);
        rules.extend(self.infer_equal_fact_subtractive_cancellation(equal_fact, verify_state)?);
        rules.extend(self.infer_equal_fact_nonzero_factor_cancellation(equal_fact, verify_state)?);
        rules.extend(self.infer_equal_fact_division_cancellation(equal_fact, verify_state)?);
        if let Some(pow) = self.infer_equal_fact_positive_real_power(equal_fact, verify_state)? {
            rules.push(InferEqualityResult::PositiveRealPower(pow));
        }
        Ok(rules)
    }
}

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/equality_cancellation/tests.rs"]
mod equality_cancellation_tests;

#[cfg(test)]
#[path = "../../../../../tests/unit/execute/nonadditive_cancellation_capture/tests.rs"]
mod nonadditive_cancellation_capture_tests;
