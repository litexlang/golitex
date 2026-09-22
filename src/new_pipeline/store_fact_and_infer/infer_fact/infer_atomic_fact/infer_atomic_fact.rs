use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // EqualFact → equal-fact infer; other atomics → except-equality stage pipeline.
    // Example: `s = cart(R, R)` takes the equal branch; `x $in S` takes except-equality.
    pub(crate) fn infer_atomic_fact(&mut self, atomic_fact: &AtomicFact) -> RuntimeResult<()> {
        match atomic_fact {
            AtomicFact::EqualFact(equal_fact) => self.infer_equal_fact(equal_fact),
            _ => self.infer_atomic_except_equality(atomic_fact),
        }
    }
}
