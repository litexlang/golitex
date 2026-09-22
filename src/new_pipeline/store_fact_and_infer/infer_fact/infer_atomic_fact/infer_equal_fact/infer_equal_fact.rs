use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferEqualFactResult;

impl Runtime {
    // Additive stages for a stored equal fact.
    // Example: `s = cart(R, R)` stores `$is_cart(s)` and `cart_dim(s) = 2`.
    pub(crate) fn infer_equal_fact(
        &mut self,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<InferEqualFactResult> {
        Ok(InferEqualFactResult {
            cart_tuple_shape: self.infer_equal_fact_cart_tuple_shape(equal_fact)?,
        })
    }
}
