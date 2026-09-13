use crate::new_pipeline::execute::execute_fact_stmt::cache_search_proof::CacheSearchProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::search_proof::
    VerifyAtomicFactSearchProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_atomic_fact::well_defined::
    DraftAtomicFactWellDefinedProof;
use crate::new_pipeline::execute::execute_fact_stmt::verify_fact_result::VerifyFactResult;
use crate::new_pipeline::execute::execute_fact_stmt::VerifyState;
use crate::new_pipeline::runtime::runtime_ids::FactId;
use crate::new_pipeline::runtime::{Runtime, RuntimeError, RuntimeResult};
use crate::prelude::*;

use super::by_builtin_algebraic_rewrite_result::*;
use super::by_builtin_rule_result::*;
use super::by_builtin_strategy_result::*;
use super::by_known_algebraic_rewrite_result::*;

pub struct DraftVerifyEqualityResult {
    pub fact: EqualFact,
    pub well_defined_proof: DraftAtomicFactWellDefinedProof,
    pub searched_proof: DraftEqualitySearchedProof,
}

pub enum DraftEqualitySearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(EqualitySearchProofByBuiltinRule),
    ByKnownAtomicFact(DraftEqualitySearchedProofByKnownAtomicFact),
    ByBuiltinStrategy(EqualitySearchProofByBuiltinStrategy),
    ByKnownForallFact(DraftEqualitySearchedProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(EqualitySearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(EqualitySearchProofByKnownAlgebraicRewrite),
}

pub struct DraftEqualitySearchedProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct DraftEqualitySearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    pub fn verify_draft_equal_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<DraftVerifyEqualityResult> {
        let well_defined_proof =
            self.verify_draft_atomic_fact_well_definedness(&fact.clone().into(), verify_state.clone())?;
        let searched_proof = match self.verify_atomic_fact_search_proof(
            &fact.clone().into(),
            verify_state,
        )? {
            VerifyAtomicFactSearchProof::Equality(proof) => proof,
            VerifyAtomicFactSearchProof::NonEquationalAtomicFact(_) => {
                unreachable!("an EqualFact must use the equality search pipeline")
            }
        };
        Ok(DraftVerifyEqualityResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_draft_equal_fact_proof(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<DraftEqualitySearchedProof> {
        let _visible_environment_count = self.current_atomic_fact_search_environment_count();

        if let Some(result) = self.search_draft_equal_fact_proof_by_cache(fact, verify_state.clone())? {
            return Ok(DraftEqualitySearchedProof::ByCache(result));
        }

        if let Some(result) =
            self.search_draft_equal_fact_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(DraftEqualitySearchedProof::ByBuiltinRule(result));
        }

        if let Some(result) =
            self.search_draft_equal_fact_proof_by_known_atomic_fact(fact, verify_state.clone())?
        {
            return Ok(DraftEqualitySearchedProof::ByKnownAtomicFact(result));
        }

        if let Some(result) =
            self.search_draft_equal_fact_proof_by_builtin_strategy(fact, verify_state.clone())?
        {
            return Ok(DraftEqualitySearchedProof::ByBuiltinStrategy(result));
        }

        if let Some(result) =
            self.search_draft_equal_fact_proof_by_known_forall_fact(fact, verify_state.clone())?
        {
            return Ok(DraftEqualitySearchedProof::ByKnownForallFact(result));
        }

        if let Some(result) =
            self.search_draft_equal_fact_proof_by_builtin_algebraic_rewrite(fact, verify_state.clone())?
        {
            return Ok(DraftEqualitySearchedProof::ByBuiltinAlgebraicRewrite(result));
        }

        if verify_state.can_use_known_algebraic_rewrite {
            if let Some(result) =
                self.search_draft_equal_fact_proof_by_known_algebraic_rewrite(fact, verify_state)?
            {
                return Ok(DraftEqualitySearchedProof::ByKnownAlgebraicRewrite(result));
            }
        }

        Err(RuntimeError::Unknown(
            "search_proof: no equality proof found".to_string(),
        ))
    }

    pub fn search_draft_equal_fact_proof_by_cache(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CacheSearchProof>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_draft_equal_fact_proof_by_builtin_rule(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_draft_equal_fact_proof_by_known_atomic_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<DraftEqualitySearchedProofByKnownAtomicFact>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_draft_equal_fact_proof_by_builtin_strategy(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinStrategy>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_draft_equal_fact_proof_by_known_forall_fact(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<DraftEqualitySearchedProofByKnownForallFact>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_draft_equal_fact_proof_by_builtin_algebraic_rewrite(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByBuiltinAlgebraicRewrite>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_draft_equal_fact_proof_by_known_algebraic_rewrite(
        &mut self,
        fact: &EqualFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<EqualitySearchProofByKnownAlgebraicRewrite>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
