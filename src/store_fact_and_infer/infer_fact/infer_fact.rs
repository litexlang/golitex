use crate::ast::fact::Fact;
use crate::runtime::{Runtime, RuntimeResult};
use crate::store_fact_and_infer::InferResult;

impl Runtime {
    // Derive extra facts from an already-stored fact; each derived fact goes through
    // `store_inferred_fact` (direct store under the named rule).
    // Example: after storing `a $in {x R: x > 0}`, infer also stores `a $in R` and `a > 0`.
    pub fn infer_fact(
        &mut self,
        fact: &Fact,
        verify_state: crate::execute::execute_fact_stmt::VerifyState,
    ) -> RuntimeResult<InferResult> {
        // Genuine premise checks cannot start another inference chain.
        let verify_state = verify_state.without_inference();
        match fact {
            Fact::AtomicFact(atomic) => Ok(InferResult::AtomicFact(
                self.infer_atomic_fact(atomic, verify_state)?,
            )),
            Fact::AndFact(and_fact) => Ok(InferResult::AndFact(
                self.infer_and_fact(and_fact, verify_state)?,
            )),
            Fact::ChainFact(chain_fact) => Ok(InferResult::ChainFact(
                self.infer_chain_fact(chain_fact, verify_state)?,
            )),
            Fact::OrFact(or_fact) => Ok(InferResult::OrFact(self.infer_or_fact(or_fact)?)),
            Fact::ExistFact(plain) => {
                Ok(InferResult::ExistFact(self.infer_plain_exist_fact(plain)?))
            }
            Fact::ExistUniqueFact(plain) => Ok(InferResult::ExistUniqueFact(
                self.infer_exist_unique_fact(plain, verify_state)?,
            )),
            Fact::NotExistFact(plain) => Ok(InferResult::NotExistFact(
                self.infer_not_exist_fact(plain, verify_state)?,
            )),
            Fact::NotForall(not_forall) => Ok(InferResult::NotForall(
                self.infer_not_forall_fact(not_forall, verify_state)?,
            )),
            Fact::ForallFact(forall) => {
                Ok(InferResult::ForallFact(self.infer_forall_fact(forall)?))
            }
            Fact::ForallFactWithIff(forall_iff) => Ok(InferResult::ForallFactWithIff(
                self.infer_forall_fact_with_iff(forall_iff)?,
            )),
        }
    }
}
