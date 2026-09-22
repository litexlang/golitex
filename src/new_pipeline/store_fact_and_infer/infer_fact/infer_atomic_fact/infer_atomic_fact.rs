use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferAtomicFactResult;

impl Runtime {
    // EqualFact → equal-fact infer; other atomics → except-equality infer.
    // Example: `s = cart(R, R)` takes the equal branch; `x $in S` takes except-equality.
    pub(crate) fn infer_atomic_fact(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> RuntimeResult<InferAtomicFactResult> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => {
                Ok(InferAtomicFactResult::EqualFact(self.infer_equal_fact(equal_fact)?))
            }
            _ => Ok(InferAtomicFactResult::ExceptEquality(
                self.infer_atomic_except_equality(atomic_fact)?,
            )),
        }
    }
}
