use crate::new_pipeline::ast::fact::{AtomicFact, EqualFact, IsCartFact, IsTupleFact};
use crate::new_pipeline::ast::obj::{
    Cart, CartDim, Literal, Number, Obj, ProductShape, Tuple, TupleDim,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Equal-fact stage: literal cart/tuple side records shape facts on the other side.
    // Example: store `s = cart(R, R)` also stores `$is_cart(s)` and `cart_dim(s) = 2`.
    pub(super) fn infer_equal_fact_cart_tuple_shape(
        &mut self,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<()> {
        if let Obj::ProductShape(ProductShape::Cart(cart)) = &equal_fact.left {
            self.infer_equal_fact_cart_from_known_side(cart, &equal_fact.right, equal_fact)?;
        }
        if let Obj::ProductShape(ProductShape::Cart(cart)) = &equal_fact.right {
            self.infer_equal_fact_cart_from_known_side(cart, &equal_fact.left, equal_fact)?;
        }
        if let Obj::ProductShape(ProductShape::Tuple(tuple)) = &equal_fact.left {
            self.infer_equal_fact_tuple_from_known_side(tuple, &equal_fact.right, equal_fact)?;
        } else if let Obj::ProductShape(ProductShape::Tuple(tuple)) = &equal_fact.right {
            self.infer_equal_fact_tuple_from_known_side(tuple, &equal_fact.left, equal_fact)?;
        }
        Ok(())
    }

    // Infer: `target = cart(...)` ⇒ `$is_cart(target)` and `cart_dim(target) = n`.
    fn infer_equal_fact_cart_from_known_side(
        &mut self,
        known_cart: &Cart,
        target: &Obj,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<()> {
        let is_cart = AtomicFact::IsCartFact(IsCartFact {
            fact_id: self.ids.allocate_fact_id(),
            set: target.clone(),
            line_file: equal_fact.line_file.clone(),
        });
        self.store_atomic_fact(&is_cart)?;

        let dim_equal = AtomicFact::EqualFact(EqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left: Obj::ProductShape(ProductShape::CartDim(CartDim {
                set: Box::new(target.clone()),
            })),
            right: Obj::Literal(Literal::Number(Number {
                normalized_value: known_cart.args.len().to_string(),
            })),
            line_file: equal_fact.line_file.clone(),
        });
        self.store_atomic_fact(&dim_equal)?;
        Ok(())
    }

    // Infer: `target = (…)` with len >= 2 ⇒ `$is_tuple(target)` and `tuple_dim(target) = n`.
    fn infer_equal_fact_tuple_from_known_side(
        &mut self,
        known_tuple: &Tuple,
        target: &Obj,
        equal_fact: &EqualFact,
    ) -> RuntimeResult<()> {
        if known_tuple.args.len() < 2 {
            return Ok(());
        }
        let is_tuple = AtomicFact::IsTupleFact(IsTupleFact {
            fact_id: self.ids.allocate_fact_id(),
            set: target.clone(),
            line_file: equal_fact.line_file.clone(),
        });
        self.store_atomic_fact(&is_tuple)?;

        let dim_equal = AtomicFact::EqualFact(EqualFact {
            fact_id: self.ids.allocate_fact_id(),
            left: Obj::ProductShape(ProductShape::TupleDim(TupleDim {
                arg: Box::new(target.clone()),
            })),
            right: Obj::Literal(Literal::Number(Number {
                normalized_value: known_tuple.args.len().to_string(),
            })),
            line_file: equal_fact.line_file.clone(),
        });
        self.store_atomic_fact(&dim_equal)?;
        Ok(())
    }
}
