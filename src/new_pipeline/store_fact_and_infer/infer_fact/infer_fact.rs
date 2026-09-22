use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::InferFactResult;

impl Runtime {
    // Derive routine consequences from an already-stored fact; store each new fact.
    // Example: after storing `a $in {x R: x > 0}`, infer also stores `a $in R` and `a > 0`.
    pub fn infer_fact(&mut self, fact: &Fact) -> RuntimeResult<InferFactResult> {
        match fact {
            Fact::AtomicFact(atomic) => {
                self.infer_atomic_fact(atomic)?;
                Ok(InferFactResult::Empty)
            }
            Fact::AndFact(and_fact) => self.infer_and_fact(and_fact),
            Fact::ChainFact(chain_fact) => self.infer_chain_fact(chain_fact),
            Fact::OrFact(_) => Ok(InferFactResult::Empty),
            Fact::ExistFact(_) | Fact::ExistUniqueFact(_) | Fact::NotExistFact(_) => {
                Ok(InferFactResult::Empty)
            }
            Fact::NotForall(not_forall) => self.infer_not_forall_fact(not_forall),
            Fact::ForallFact(_) | Fact::ForallFactWithIff(_) => Ok(InferFactResult::Empty),
        }
    }
}
