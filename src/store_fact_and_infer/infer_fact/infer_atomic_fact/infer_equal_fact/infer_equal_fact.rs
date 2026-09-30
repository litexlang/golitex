use crate::ast::fact::EqualFact;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferEqualityResult;

impl Runtime {
    // Collect every equality-infer rule that fires for a stored equal fact.
    // Example: `s = cart(R, R)` pushes CartTupleShape with `$is_cart(s)` and dim.
    pub(crate) fn infer_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<Vec<InferEqualityResult>> {
        let mut rules = Vec::new();
        if let Some(shape) = self.infer_equal_fact_cart_tuple_shape(equal_fact)? {
            rules.push(InferEqualityResult::CartTupleShape(shape));
        }
        if let Some(pow) = self.infer_equal_fact_positive_real_power(equal_fact)? {
            rules.push(InferEqualityResult::PositiveRealPower(pow));
        }
        if let Some(linear) = self.infer_equal_fact_simple_linear_solved_value(equal_fact)? {
            rules.push(InferEqualityResult::SimpleLinearSolvedValue(linear));
        }
        Ok(rules)
    }
}
