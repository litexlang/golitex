use crate::prelude::*;

impl Runtime {
    /// Dispatch infer by atomic fact type.
    /// Example: `x $in S` enters membership infer.
    pub(crate) fn infer_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<InferResult, RuntimeError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.infer_equal_fact(equal_fact),
            AtomicFact::InFact(in_fact) => self.infer_in_fact(in_fact),
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => {
                self.infer_normal_atomic_fact(normal_atomic_fact)
            }
            AtomicFact::SubsetFact(subset_fact) => self.infer_subset_fact(subset_fact),
            AtomicFact::SupersetFact(superset_fact) => self.infer_superset_fact(superset_fact),
            AtomicFact::LessFact(_)
            | AtomicFact::GreaterFact(_)
            | AtomicFact::LessEqualFact(_)
            | AtomicFact::GreaterEqualFact(_) => {
                self.infer_numeric_order_sign_from_order_atomic(atomic_fact)
            }
            _ => Ok(InferResult::new()),
        }
    }
}
