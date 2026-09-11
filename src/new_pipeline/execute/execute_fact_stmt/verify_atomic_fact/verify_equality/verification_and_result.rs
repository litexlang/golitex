use crate::new_pipeline::execute::execute_fact_stmt::cache_search_proof::CacheSearchProof2;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::search_proof::
    VerifyAtomicFactSearchProof2;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::well_defined::
    AtomicFactWellDefinedProof2;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult2;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState2;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::prelude::*;

use super::by_builtin_algebraic_rewrite_result::*;
use super::by_builtin_rule_result::*;
use super::by_builtin_strategy_result::*;
use super::by_known_algebraic_rewrite_result::*;

pub struct VerifyEqualityResult2 {
    pub fact: EqualFact,
    pub well_defined_proof: AtomicFactWellDefinedProof2,
    pub searched_proof: EqualitySearchedProof2,
}

pub enum EqualitySearchedProof2 {
    ByCache(CacheSearchProof2),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule2),
    ByKnownAtomicFact(EqualitySearchedProofByKnownAtomicFact2),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy2),
    ByKnownForallFact(EqualitySearchedProofByKnownForallFact2),
    ByBuiltinAlgebraicRewrite(EqualitySearchProofByBuiltinAlgebraicRewrite2),
    ByKnownAlgebraicRewrite(EqualitySearchProofByKnownAlgebraicRewrite2),
}

pub struct EqualitySearchedProofByKnownAtomicFact2 {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult2>,
}

pub struct EqualitySearchedProofByKnownForallFact2 {
    pub cite_fact_id: FactId,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_equal_fact2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<VerifyEqualityResult2> {
        let well_defined_proof =
            self.verify_atomic_fact_well_definedness2(&fact.clone().into(), verify_state.clone())?;
        let searched_proof = match self.verify_atomic_fact_search_proof(
            &fact.clone().into(),
            verify_state,
        )? {
            VerifyAtomicFactSearchProof2::Equality(proof) => proof,
            VerifyAtomicFactSearchProof2::NonEquationalAtomicFact(_) => {
                unreachable!("an EqualFact must use the equality search pipeline")
            }
        };
        Ok(VerifyEqualityResult2 {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_equal_fact_proof2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<EqualitySearchedProof2> {
        let _visible_environment_count = self.current_atomic_fact_search_environment_count();

        if let Some(result) = self.search_equal_fact_proof_by_cache2(fact, verify_state.clone())? {
            return Ok(EqualitySearchedProof2::ByCache(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_rule2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByBuiltinRule(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_atomic_fact2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByKnownAtomicFact(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_strategy2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByBuiltinStrategy(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_known_forall_fact2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByKnownForallFact(result));
        }

        if let Some(result) =
            self.search_equal_fact_proof_by_builtin_algebraic_rewrite2(fact, verify_state.clone())?
        {
            return Ok(EqualitySearchedProof2::ByBuiltinAlgebraicRewrite(result));
        }

        if verify_state.can_use_known_algebraic_rewrite {
            if let Some(result) =
                self.search_equal_fact_proof_by_known_algebraic_rewrite2(fact, verify_state)?
            {
                return Ok(EqualitySearchedProof2::ByKnownAlgebraicRewrite(result));
            }
        }

        Err(RuntimeError::Unknown(
            "search_proof: no equality proof found".to_string(),
        ))
    }

    pub fn search_equal_fact_proof_by_cache2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<CacheSearchProof2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_builtin_rule2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRule2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_known_atomic_fact2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<EqualitySearchedProofByKnownAtomicFact2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_builtin_strategy2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinStrategy2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_known_forall_fact2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<EqualitySearchedProofByKnownForallFact2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_builtin_algebraic_rewrite2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinAlgebraicRewrite2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_equal_fact_proof_by_known_algebraic_rewrite2(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<EqualitySearchProofByKnownAlgebraicRewrite2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
