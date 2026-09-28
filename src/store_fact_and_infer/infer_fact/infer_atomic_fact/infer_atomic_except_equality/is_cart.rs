use crate::ast::fact::{AtomicFact, Fact, GreaterEqualFact, IsCartFact};
use crate::ast::obj::{CartDim, Literal, Number, Obj, ProductShape};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferIsCartDimensionLowerBoundResult;

impl Runtime {
    // When: stored `$is_cart(C)`.
    // Infers: `cart_dim(C) >= 2`.
    pub(super) fn infer_is_cart_dimension_lower_bound(
        &mut self,
        is_cart: &IsCartFact,
    ) -> RuntimeResult<InferIsCartDimensionLowerBoundResult> {
        let lower_bound = AtomicFact::GreaterEqualFact(GreaterEqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: Obj::ProductShape(ProductShape::CartDim(CartDim {
                set: Box::new(is_cart.set.clone()),
            })),
            right: Obj::Literal(Literal::Number(Number {
                normalized_value: "2".to_string(),
            })),
            line_file: is_cart.line_file.clone(),
        });
        let derived = Box::new(
            self.store_inferred_fact_and_infer(&Fact::AtomicFact(lower_bound))?,
        );
        Ok(InferIsCartDimensionLowerBoundResult { derived })
    }
}
