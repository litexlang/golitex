use crate::prelude::*;

impl Runtime {
    // Dispatch `infer` for a single atomic fact (see `docs/Manual.md#builtin-inference`).
    pub fn infer_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        let fact_key = nested_obj_binder_normalized_fact_key(&atomic_fact.clone().into());
        // Recursive inference may return to the same membership through an
        // alpha-renamed set builder. This is a DFS back-edge guard, not an
        // inference-depth limit: distinct nested facts still expand normally.
        if !self.active_atomic_fact_inferences.insert(fact_key.clone()) {
            return Ok(InferResult::new());
        }

        let result = match atomic_fact {
            // Equality: numeric bindings, cart/tuple/seq/matrix structure, `0 = a - b` => `a = b`.
            AtomicFact::EqualFact(equal_fact) => self.infer_equal_fact(equal_fact),
            // A stored global function equality is ordinary object equality.
            // Example: `$fn_eq(f, g)` infers `f = g`, which then supports congruence.
            AtomicFact::FnEqualFact(fn_equal_fact) => {
                let inferred_equality: AtomicFact = EqualFact::new(
                    fn_equal_fact.left.clone(),
                    fn_equal_fact.right.clone(),
                    fn_equal_fact.line_file.clone(),
                )
                .into();
                let reason = InferReason::InferRule("fn_eq implies ordinary equality".to_string());
                self.store_atomic_fact_without_well_defined_verified_and_infer_with_reason(
                    inferred_equality,
                    reason.store_reason(),
                )
            }
            // Membership `x $in S`: unfold `S` (list, set builder, intervals, standard sets, …).
            AtomicFact::InFact(in_fact) => self.infer_in_fact(in_fact),
            // A Cartesian product has at least two coordinates.
            AtomicFact::IsCartFact(is_cart_fact) => {
                self.infer_is_cart_dimension_lower_bound(is_cart_fact)
            }
            // Predicate atom `P(...)`: parameter typing plus each `iff` clause from `P`'s definition.
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => {
                self.infer_normal_atomic_fact(normal_atomic_fact)
            }
            // `A $subset B` => `forall` fresh `x $in A: x $in B`.
            AtomicFact::SubsetFact(subset_fact) => self.infer_subset_fact(subset_fact),
            // `A $superset B` => `forall` fresh `x $in B: x $in A`.
            AtomicFact::SupersetFact(superset_fact) => self.infer_superset_fact(superset_fact),
            // One-sided numeric comparison: if the other side is a resolved constant, infer sign vs 0.
            AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                self.infer_numeric_order_sign_from_order_atomic(atomic_fact)
            }
            // e.g. negated atoms and `$is_set`: no inference on this path.
            _ => Ok(InferResult::new()),
        };

        self.active_atomic_fact_inferences.remove(&fact_key);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fn_eq_infers_ordinary_equality_for_known_congruence() {
        let mut runtime = Runtime::new();
        runtime.new_file_path_new_env_new_name_scope("fn_eq_infers_ordinary_equality");

        let f: Obj = Identifier::new("f".to_string()).into();
        let g: Obj = Identifier::new("g".to_string()).into();
        let line_file = default_line_file();
        let fn_eq: AtomicFact = FnEqualFact::new(f.clone(), g.clone(), line_file.clone()).into();
        let ordinary_equality: Fact =
            EqualFact::new(f.clone(), g.clone(), line_file.clone()).into();

        let infer_result = runtime
            .store_atomic_fact_without_well_defined_verified_and_infer(fn_eq)
            .expect("store fn_eq and infer ordinary equality");
        assert!(infer_result.contains_added_fact(&ordinary_equality));
        assert!(runtime
            .verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                &f,
                &g,
                line_file.clone()
            ))
            .is_true());

        let left_power_set: Obj = PowerSet::new(f).into();
        let right_power_set: Obj = PowerSet::new(g).into();
        assert!(runtime
            .verify_equal_fact_by_known_equality(&EqualFact::new_from_refs(
                &left_power_set,
                &right_power_set,
                line_file
            ))
            .is_true());
    }
}
