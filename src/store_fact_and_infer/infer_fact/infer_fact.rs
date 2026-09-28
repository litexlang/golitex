use crate::ast::fact::Fact;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferFactResult;

impl Runtime {
    // Derive extra facts from an already-stored fact; each derived fact goes through
    // `store_inferred_fact_and_infer` (WD then store+infer).
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
            Fact::OrFact(or_fact) => Ok(InferFactResult::OrFact(self.infer_or_fact(or_fact)?)),
            Fact::ExistFact(_) | Fact::ExistUniqueFact(_) | Fact::NotExistFact(_) => Ok(
                InferFactResult::ExistShapedFact(self.infer_exist_shaped_fact(fact)?),
            ),
            Fact::NotForall(not_forall) => {
                Ok(InferFactResult::NotForallFact(self.infer_not_forall_fact(not_forall)?))
            }
            Fact::ForallFact(forall) => {
                Ok(InferFactResult::ForallFact(self.infer_forall_fact(forall)?))
            }
            Fact::ForallFactWithIff(forall_iff) => Ok(InferFactResult::ForallFactWithIff(
                self.infer_forall_fact_with_iff(forall_iff)?,
            )),
        }
    }
}
