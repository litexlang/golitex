use crate::ast::fact::{
    AtomicFact, Fact, GreaterEqualFact, LessEqualFact,
};
use crate::ast::obj::{Literal, Number, Obj};
use crate::rational_expression::{
    compare_closed_objs_by_normalized_decimal, evaluate_obj_to_normalized_decimal_number,
    NumberCompareResult,
};
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::{
    InferOrderDualAndNonnegLowerBoundResult, StoreFactAndInferResult,
};

impl Runtime {
    // When: stored `x >= c` with closed numeric `c`.
    // Infers: dual `c <= x`, and if `0 <= c` also `0 <= x`.
    // Example: store `t >= 10` ⇒ `10 <= t` and `0 <= t`.
    pub(super) fn infer_greater_equal_order_dual_and_nonneg_lower(
        &mut self,
        fact: &GreaterEqualFact,
    ) -> RuntimeResult<Option<InferOrderDualAndNonnegLowerBoundResult>> {
        let mut derived = Vec::new();
        if evaluate_obj_to_normalized_decimal_number(&fact.right).is_none() {
            return Ok(None);
        }
        let dual_id = self.global_ids.allocate_fact_id();
        if let Some(stored) = self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(
            AtomicFact::LessEqualFact(LessEqualFact {
                fact_id: dual_id,
                left: fact.right.clone(),
                right: fact.left.clone(),
                line_file: fact.line_file.clone(),
            }),
        ))? {
            derived.push(stored);
        }
        if closed_obj_is_nonnegative(&fact.right) {
            if let Some(stored) = self.try_store_nonneg_lower_bound(&fact.left, &fact.line_file)? {
                derived.push(stored);
            }
        }
        if derived.is_empty() {
            return Ok(None);
        }
        Ok(Some(InferOrderDualAndNonnegLowerBoundResult { derived }))
    }

    // When: stored `c <= x` with closed numeric `c` and `0 <= c`.
    // Infers: `0 <= x`.
    // Example: store `10 <= t` ⇒ `0 <= t`.
    pub(super) fn infer_less_equal_nonneg_lower_from_closed_bound(
        &mut self,
        fact: &LessEqualFact,
    ) -> RuntimeResult<Option<InferOrderDualAndNonnegLowerBoundResult>> {
        if evaluate_obj_to_normalized_decimal_number(&fact.left).is_none() {
            return Ok(None);
        }
        if !closed_obj_is_nonnegative(&fact.left) {
            return Ok(None);
        }
        let Some(stored) = self.try_store_nonneg_lower_bound(&fact.right, &fact.line_file)? else {
            return Ok(None);
        };
        Ok(Some(InferOrderDualAndNonnegLowerBoundResult {
            derived: vec![stored],
        }))
    }

    fn try_store_nonneg_lower_bound(
        &mut self,
        obj: &Obj,
        line_file: &Option<crate::ast::line_file::SourceLine>,
    ) -> RuntimeResult<Option<StoreFactAndInferResult>> {
        let zero = Obj::Literal(Literal::Number(Number {
            normalized_value: "0".to_string(),
        }));
        if obj.ir() == zero.ir() {
            return Ok(None);
        }
        let fact_id = self.global_ids.allocate_fact_id();
        self.try_store_inferred_fact_and_infer(&Fact::AtomicFact(AtomicFact::LessEqualFact(
            LessEqualFact {
                fact_id,
                left: zero,
                right: obj.clone(),
                line_file: line_file.clone(),
            },
        )))
    }
}

fn closed_obj_is_nonnegative(obj: &Obj) -> bool {
    let zero = Obj::Literal(Literal::Number(Number {
        normalized_value: "0".to_string(),
    }));
    match compare_closed_objs_by_normalized_decimal(&zero, obj) {
        Some((NumberCompareResult::Less, _, _))
        | Some((NumberCompareResult::Equal, _, _)) => true,
        _ => false,
    }
}
