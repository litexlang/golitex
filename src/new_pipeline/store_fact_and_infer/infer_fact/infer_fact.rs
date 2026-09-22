use crate::new_pipeline::ast::fact::Fact;
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};
use crate::new_pipeline::store_fact_and_infer::{
    InferExistShapedFactResult, InferFactResult, InferForallFactResult,
    InferForallFactWithIffResult, InferOrFactResult,
};

impl Runtime {
    // Derive extra facts from an already-stored fact; each derived fact is stored.
    // Example: after storing `a $in {x R: x > 0}`, infer also stores `a $in R` and `a > 0`.
    pub fn infer_fact(&mut self, fact: &Fact) -> RuntimeResult<InferFactResult> {
        match fact {
            Fact::AtomicFact(atomic) => {
                Ok(InferFactResult::AtomicFact(self.infer_atomic_fact(atomic)?))
            }
            Fact::AndFact(and_fact) => Ok(InferFactResult::AndFact(self.infer_and_fact(and_fact)?)),
            Fact::ChainFact(chain_fact) => {
                Ok(InferFactResult::ChainFact(self.infer_chain_fact(chain_fact)?))
            }
            Fact::OrFact(_) => Ok(InferFactResult::OrFact(InferOrFactResult {})),
            Fact::ExistFact(_) | Fact::ExistUniqueFact(_) | Fact::NotExistFact(_) => {
                Ok(InferFactResult::ExistShapedFact(InferExistShapedFactResult {}))
            }
            Fact::NotForall(not_forall) => {
                Ok(InferFactResult::NotForallFact(self.infer_not_forall_fact(not_forall)?))
            }
            Fact::ForallFact(_) => Ok(InferFactResult::ForallFact(InferForallFactResult {})),
            Fact::ForallFactWithIff(_) => {
                Ok(InferFactResult::ForallFactWithIff(InferForallFactWithIffResult {}))
            }
        }
    }
}
