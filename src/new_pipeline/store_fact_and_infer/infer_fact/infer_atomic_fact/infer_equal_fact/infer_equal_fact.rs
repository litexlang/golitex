use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferEqualityResult;

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
        if let Some(sub) = self.infer_equal_fact_subtraction_equals_zero(equal_fact)? {
            rules.push(InferEqualityResult::SubtractionEqualsZero(sub));
        }
        Ok(rules)
    }
}
