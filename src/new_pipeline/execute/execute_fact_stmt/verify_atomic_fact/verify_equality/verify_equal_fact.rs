use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    EqualFactSearchedProof, SearchProofByKnownForallFact, VerifyEqualityResult,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::{
    VerifyAtomicFactWellDefinedResult, VerifyState,
};
use crate::new_pipeline::runtime::{Runtime, RuntimeResult};

use super::EqualitySearchProofByBuiltinStrategy;

impl Runtime {
    pub fn verify_equal_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyFactResult> {
        let well_defined_proof = match self
            .verify_atomic_fact_well_definedness(&(fact.clone().into()), verify_state.clone())?
        {
            VerifyAtomicFactWellDefinedResult::Success(proof) => proof,
            VerifyAtomicFactWellDefinedResult::Failed(_) => {
                return Ok(VerifyFactResult::FailToVerifyWellDefined);
            }
        };
        match self.search_equal_fact_proof(fact, verify_state)? {
            Some(searched_proof) => {
                Ok(VerifyFactResult::Equality(Box::new(VerifyEqualityResult {
                    fact: fact.clone(),
                    well_defined_proof,
                    searched_proof,
                })))
            }
            None => Ok(VerifyFactResult::FailToSearchProof),
        }
    }

    // Stage order: builtin rule → known equality → builtin strategy →
    // known forall → (if allowed) builtin algebraic rewrite →
    // known algebraic rewrite.
    // Algebraic rewrite replaces legacy opaque resolve_obj.
    // Ok(None) means no proof found; that is not a runtime error.
    pub fn search_equal_fact_proof(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualFactSearchedProof>> {
        if let Some(result) =
            self.search_equal_fact_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinRule(result)));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_equality(fact, verify_state.clone())?
        {
            return Ok(Some(EqualFactSearchedProof::ByKnownEquality(result)));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_strategy(fact, verify_state.clone())?
        {
            return Ok(Some(EqualFactSearchedProof::ByBuiltinStrategy(result)));
        }

        if verify_state.can_use_forall_fact {
            if let Some(result) = self
                .search_equal_fact_proof_by_known_forall_fact(fact, verify_state.clone())?
            {
                return Ok(Some(EqualFactSearchedProof::ByKnownForallFact(result)));
            }
        }

        if verify_state.can_use_algebraic_rewrite {
            if let Some(result) = self
                .search_equal_fact_proof_by_builtin_algebraic_rewrite(
                    fact,
                    verify_state.clone(),
                )?
            {
                return Ok(Some(EqualFactSearchedProof::ByBuiltinAlgebraicRewrite(
                    result,
                )));
            }

            if let Some(result) = self
                .search_equal_fact_proof_by_known_algebraic_rewrite(fact, verify_state)?
            {
                return Ok(Some(EqualFactSearchedProof::ByKnownAlgebraicRewrite(
                    result,
                )));
            }
        }

        Ok(None)
    }

    pub fn search_equal_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinStrategy>> {
        if let Some(proof) =
            self.search_equal_fact_by_rational_with_nonzero_premises(fact, verify_state)?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
            ));
        }
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<SearchProofByKnownForallFact>> {
        self.search_atomic_fact_proof_by_known_forall_fact(&(fact.clone().into()), verify_state)
    }
}
