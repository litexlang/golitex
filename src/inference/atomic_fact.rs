use crate::prelude::*;

impl Runtime {
    // Dispatch `infer` for a single atomic fact (see `docs/Manual.md#builtin-inference`).
    pub(in crate::inference) fn atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
        inference_state: &InferenceState,
    ) -> Result<SuccessInferResult, RuntimeError> {
        // Recursive inference may return to the same membership through an
        // alpha-renamed set builder. This guards a DFS back-edge, not depth.
        let Some(_active_inference) = inference_state.enter_atomic_fact(atomic_fact) else {
            return Ok(SuccessInferResult::new());
        };

        match atomic_fact {
            // Equality: numeric bindings, cart/tuple/seq/matrix structure, `0 = a - b` => `a = b`.
            AtomicFact::EqualFact(equal_fact) => self.infer_equal_fact(equal_fact, inference_state),
            // A stored global function equality is ordinary object equality.
            // Example: `$fn_eq(f, g)` infers `f = g`, which then supports congruence.
            AtomicFact::FnEqualFact(fn_equal_fact) => {
                let inferred_equality: AtomicFact = self
                    .new_equal_fact(
                        fn_equal_fact.left.clone(),
                        fn_equal_fact.right.clone(),
                        fn_equal_fact.line_file.clone(),
                    )
                    .into();
                let reason = InferReason::InferRule("fn_eq implies ordinary equality".to_string());
                self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason_and_state(
                    inferred_equality,
                    reason.store_reason(),
                    inference_state,
                )
            }
            // Membership `x $in S`: unfold `S` (list, set builder, intervals, standard sets, …).
            AtomicFact::InFact(in_fact) => self.membership(in_fact, inference_state),
            // A Cartesian product has at least two coordinates.
            AtomicFact::IsCartFact(is_cart_fact) => {
                self.infer_is_cart_dimension_lower_bound(is_cart_fact, inference_state)
            }
            // Predicate atom `P(...)`: parameter typing plus each `iff` clause from `P`'s definition.
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => {
                self.infer_normal_atomic_fact(normal_atomic_fact, inference_state)
            }
            // `A $subset B` => `forall` fresh `x $in A: x $in B`.
            AtomicFact::SubsetFact(subset_fact) => {
                self.infer_subset_fact(subset_fact, inference_state)
            }
            // `A $superset B` => `forall` fresh `x $in B: x $in A`.
            AtomicFact::SupersetFact(superset_fact) => {
                self.infer_superset_fact(superset_fact, inference_state)
            }
            // One-sided numeric comparison: if the other side is a resolved constant, infer sign vs 0.
            AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                self.infer_numeric_order_sign_from_order_atomic(atomic_fact, inference_state)
            }
            // e.g. negated atoms and `$is_set`: no inference on this path.
            _ => Ok(SuccessInferResult::new()),
        }
    }
}

#[cfg(test)]
#[path = "../../tests/unit/inference/atomic_fact/tests.rs"]
mod tests;
