use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, Fact, IsCartFact, IsTupleFact};
use crate::new_pipeline::ast::obj::{
    Cart, CartDim, Literal, Number, Obj, ProductShape, Tuple, TupleDim,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferEqualFactCartTupleShapeResult, StoreFactAndInferResult,
};

impl Runtime {
    // Equal-fact stage: literal cart/tuple side records shape facts on the other side.
    // Example: store `s = cart(R, R)` also stores `$is_cart(s)` and `cart_dim(s) = 2`.
    pub(super) fn infer_equal_fact_cart_tuple_shape(
        &mut self,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<Option<InferEqualFactCartTupleShapeResult>> {
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();
        if let Obj::ProductShape(ProductShape::Cart(cart)) = &equal_fact.left {
            derived.extend(self.infer_equal_fact_cart_from_known_side(
                cart,
                &equal_fact.right,
                equal_fact,
            )?);
        }
        if let Obj::ProductShape(ProductShape::Cart(cart)) = &equal_fact.right {
            derived.extend(self.infer_equal_fact_cart_from_known_side(
                cart,
                &equal_fact.left,
                equal_fact,
            )?);
        }
        if let Obj::ProductShape(ProductShape::Tuple(tuple)) = &equal_fact.left {
            derived.extend(self.infer_equal_fact_tuple_from_known_side(
                tuple,
                &equal_fact.right,
                equal_fact,
            )?);
        } else if let Obj::ProductShape(ProductShape::Tuple(tuple)) = &equal_fact.right {
            derived.extend(self.infer_equal_fact_tuple_from_known_side(
                tuple,
                &equal_fact.left,
                equal_fact,
            )?);
        }
        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(InferEqualFactCartTupleShapeResult { derived }))
    }

    // Infer: `target = cart(...)` ⇒ `$is_cart(target)` and `cart_dim(target) = n`.
    fn infer_equal_fact_cart_from_known_side(
        &mut self,
        known_cart: &Cart,
        target: &Obj,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<Vec<StoreFactAndInferResult>> {
        let is_cart = AtomicFact::IsCartFact(IsCartFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: target.clone(),
            line_file: equal_fact.line_file.clone(),
        });
        let dim_equal = AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: Obj::ProductShape(ProductShape::CartDim(CartDim {
                set: Box::new(target.clone()),
            })),
            right: Obj::Literal(Literal::Number(Number {
                normalized_value: known_cart.args.len().to_string(),
            })),
            line_file: equal_fact.line_file.clone(),
        });
        Ok(vec![
            self.store_inferred_fact_and_infer(&Fact::AtomicFact(is_cart))?,
            self.store_inferred_fact_and_infer(&Fact::AtomicFact(dim_equal))?,
        ])
    }

    // Infer: `target = (…)` with len >= 2 ⇒ `$is_tuple(target)` and `tuple_dim(target) = n`.
    fn infer_equal_fact_tuple_from_known_side(
        &mut self,
        known_tuple: &Tuple,
        target: &Obj,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<Vec<StoreFactAndInferResult>> {
        if known_tuple.args.len() < 2 {
            return Ok(Vec::new());
        }
        let is_tuple = AtomicFact::IsTupleFact(IsTupleFact {
            fact_id: self.global_ids.allocate_fact_id(),
            set: target.clone(),
            line_file: equal_fact.line_file.clone(),
        });
        let dim_equal = AtomicFact::EqualFact(EqualFact {
            fact_id: self.global_ids.allocate_fact_id(),
            left: Obj::ProductShape(ProductShape::TupleDim(TupleDim {
                arg: Box::new(target.clone()),
            })),
            right: Obj::Literal(Literal::Number(Number {
                normalized_value: known_tuple.args.len().to_string(),
            })),
            line_file: equal_fact.line_file.clone(),
        });
        Ok(vec![
            self.store_inferred_fact_and_infer(&Fact::AtomicFact(is_tuple))?,
            self.store_inferred_fact_and_infer(&Fact::AtomicFact(dim_equal))?,
        ])
    }
}
