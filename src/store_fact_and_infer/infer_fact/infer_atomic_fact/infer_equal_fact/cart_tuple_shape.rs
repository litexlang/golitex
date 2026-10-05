use crate::ast::fact::{AtomicFact, EqualFact, Fact, IsTupleFact};
use crate::ast::obj::{
    Literal, Number, Obj, ProductShape, Tuple, TupleDim,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferEqualFactCartTupleShapeResult, StoreFactAndInferResult,
};

impl Runtime {
    // Transitional tuple producer only; cart is an ordinary set. Equality to
    // cart(...) cannot recover a unique construction dimension. For example,
    // both cart({}, R) and cart({}, R, Z) equal the same empty set.
    pub(super) fn infer_equal_fact_cart_tuple_shape(
        &mut self,
        equal_fact: &EqualFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Option<InferEqualFactCartTupleShapeResult>> {
        let mut derived: Vec<StoreFactAndInferResult> = Vec::new();
        if let Obj::ProductShape(ProductShape::Tuple(tuple)) = &equal_fact.left {
            derived.extend(self.infer_equal_fact_tuple_from_known_side(
                tuple,
                &equal_fact.right,
                equal_fact,
             verify_state)?);
        } else if let Obj::ProductShape(ProductShape::Tuple(tuple)) = &equal_fact.right {
            derived.extend(self.infer_equal_fact_tuple_from_known_side(
                tuple,
                &equal_fact.left,
                equal_fact,
             verify_state)?);
        }
        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(InferEqualFactCartTupleShapeResult { derived }))
    }

    // Infer: `target = (…)` with len >= 2 ⇒ `$is_tuple(target)` and `tuple_dim(target) = n`.
    fn infer_equal_fact_tuple_from_known_side(
        &mut self,
        known_tuple: &Tuple,
        target: &Obj,
        equal_fact: &EqualFact,
     verify_state: crate::execute::execute_fact_stmt::VerifyState) -> RuntimeResult<Vec<StoreFactAndInferResult>> {
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
            self.store_inferred_fact_and_infer(&Fact::AtomicFact(is_tuple), verify_state)?,
            self.store_inferred_fact_and_infer(&Fact::AtomicFact(dim_equal), verify_state)?,
        ])
    }
}
