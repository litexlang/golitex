use crate::prelude::*;

impl Runtime {
    // Dispatch `infer` for a single atomic fact (see `docs/Builtin_Features/Builtin_Inference.md`).
    pub fn infer_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        match atomic_fact {
            // Equality: numeric bindings, cart/tuple/seq/matrix structure, `0 = a - b` => `a = b`.
            AtomicFact::EqualFact(equal_fact) => self.infer_equal_fact(equal_fact),
            // Membership `x $in S`: unfold `S` (list, set builder, intervals, standard sets, …).
            AtomicFact::InFact(in_fact) => self.infer_in_fact(in_fact),
            // Predicate atom `P(...)`: parameter typing plus each `iff` clause from `P`'s definition.
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => {
                self.infer_normal_atomic_fact(normal_atomic_fact)
            }
            // `A $subset B` => `forall` fresh `x $in A: x $in B`.
            AtomicFact::SubsetFact(subset_fact) => self.infer_subset_fact(subset_fact),
            // `A $superset B` => `forall` fresh `x $in B: x $in A`.
            AtomicFact::SupersetFact(superset_fact) => self.infer_superset_fact(superset_fact),
            AtomicFact::RestrictFact(rf) => self.infer_restrict_fact(rf),
            // One-sided numeric comparison: if the other side is a resolved constant, infer sign vs 0.
            AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                self.infer_numeric_order_sign_from_order_atomic(atomic_fact)
            }
            // e.g. negated atoms, `is_set`, `not_restrict_fn_in`: no inference on this path.
            _ => Ok(InferResult::new()),
        }
    }
}
