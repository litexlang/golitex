use crate::new_pipeline::ast::fact::EqualFact;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::{
    EqualFactSearchedProof, SearchProofByKnownForallFact,
};
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::verify_equality::result::{
    equal_fact_result_from_search_fail, equal_fact_result_from_success,
    equal_fact_result_from_wd_fail,
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
            VerifyAtomicFactWellDefinedResult::Failed(reason) => {
                return Ok(equal_fact_result_from_wd_fail(reason));
            }
        };
        match self.search_equal_fact_proof(fact, verify_state)? {
            Some(searched_proof) => Ok(equal_fact_result_from_success(
                fact,
                well_defined_proof,
                searched_proof,
            )),
            None => Ok(equal_fact_result_from_search_fail(fact, well_defined_proof)),
        }
    }

    // Stage order: builtin rule → known equality → builtin strategy →
    // known forall → (if allowed) builtin rewrite →
    // known rewrite.
    // Rewrite replaces legacy opaque resolve_obj.
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
                return Ok(Some(EqualFactSearchedProof::ByKnownForallFact(Box::new(
                    result,
                ))));
            }
        }

        if verify_state.can_use_rewrite {
            if let Some(result) = self
                .search_equal_fact_proof_by_builtin_rewrite(
                    fact,
                    verify_state.clone(),
                )?
            {
                return Ok(Some(EqualFactSearchedProof::ByBuiltinRewrite(
                    result,
                )));
            }

            if let Some(result) = self
                .search_equal_fact_proof_by_known_rewrite(fact, verify_state)?
            {
                return Ok(Some(EqualFactSearchedProof::ByKnownRewrite(
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
            self.search_equal_fact_by_rational_with_nonzero_premises(fact, verify_state.clone())?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::RationalWithNonzeroPremises(proof),
            ));
        }
        if let Some(proof) =
            self.search_equal_fact_by_extremum_equality(fact, verify_state.clone())?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::ExtremumEquality(proof),
            ));
        }
        if let Some(proof) = self
            .search_equal_fact_by_finite_set_product_pointwise(fact, verify_state.clone())?
        {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::FiniteSetProductPointwiseEquality(proof),
            ));
        }
        if let Some(proof) = self.search_equal_fact_by_mod_congruence(fact, verify_state)? {
            return Ok(Some(
                EqualitySearchProofByBuiltinStrategy::ModCongruence(proof),
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
