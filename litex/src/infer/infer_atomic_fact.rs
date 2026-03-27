use crate::error::InferError;
use crate::execute::Runtime;
use crate::fact::AtomicFact;
use crate::infer::InferResult;

impl Runtime {
    /// Dispatch infer by atomic fact type.
    /// Example: `x $in S` enters membership infer.
    pub(crate) fn infer_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> Result<InferResult, InferError> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.infer_equal_fact(equal_fact),
            AtomicFact::InFact(in_fact) => self.infer_in_fact(in_fact),
            AtomicFact::NormalAtomicFact(normal_atomic_fact) => {
                self.infer_normal_atomic_fact(normal_atomic_fact)
            }
            AtomicFact::SubsetFact(subset_fact) => self.infer_subset_fact(subset_fact),
            AtomicFact::SupersetFact(superset_fact) => self.infer_superset_fact(superset_fact),
            _ => Ok(InferResult::new()),
        }
    }
}
