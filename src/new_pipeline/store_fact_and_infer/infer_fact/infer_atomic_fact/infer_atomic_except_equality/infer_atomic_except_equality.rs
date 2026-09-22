use crate::new_pipeline::ast::fact::AtomicFact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Dispatch non-equal atomic infer by fact shape.
    // - NormalAtomicFact → expand prop definition iff facts
    // - InFact → membership projections from the carrier set
    // Other shapes currently infer nothing here.
    pub(crate) fn infer_atomic_except_equality(
        &mut self,
        atomic_fact: &AtomicFact,
    ) -> RuntimeResult<()> {
        match atomic_fact {
            AtomicFact::NormalAtomicFact(normal) => {
                self.infer_expand_definition_stage(normal)
            }
            AtomicFact::InFact(in_fact) => self.infer_membership_projection_stage(in_fact),
            _ => Ok(()),
        }
    }
}
