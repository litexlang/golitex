//! Family strategy selection. All generated premises use the shared verifier.
use crate::ast::fact::{AtomicFact, EqualFact};
use crate::execute::execute_fact_stmt::verify_atomic_fact::{
    AtomicExceptEqualityFactSearchedProof, EqualFactSearchedProof,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

impl Runtime {
    // Top-level entry: builtin strategy first, then user-defined strategy.
    pub fn verify_by_strategy_atomic_except_equality(
        &mut self,
        fact: &AtomicFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchedProof>> {
        if let Some(result) =
            self.search_atomic_except_equality_fact_proof_by_builtin_strategy(fact, ctx)?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByBuiltinStrategy(result),
            ));
        }
        if let Some(result) =
            self.search_atomic_except_equality_fact_proof_by_known_strategy(fact, ctx)?
        {
            return Ok(Some(
                AtomicExceptEqualityFactSearchedProof::ByKnownStrategy(result),
            ));
        }
        Ok(None)
    }

    // Top-level equality strategy entry.
    pub fn verify_by_strategy_equal(
        &mut self,
        fact: &EqualFact,
        ctx: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        if let Some(result) = self.search_equal_fact_proof_by_builtin_strategy(fact, ctx)? {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinStrategy(result)));
        }
        Ok(None)
    }
}
