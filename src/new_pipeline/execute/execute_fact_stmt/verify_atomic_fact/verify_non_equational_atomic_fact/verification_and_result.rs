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

pub struct VerifyNonEquationalAtomicFactResult2 {
    pub fact: AtomicFact,
    pub well_defined_proof: AtomicFactWellDefinedProof2,
    pub searched_proof: NonEquationalAtomicFactSearchedProof2,
}

pub enum NonEquationalAtomicFactSearchedProof2 {
    ByCache(CacheSearchProof2),
    ByBuiltinRule(NonEquationalAtomicFactSearchProofByBuiltinRule2),
    ByKnownAtomicFact(NonEquationalAtomicFactSearchedProofByKnownAtomicFact2),
    ByDefinition(NonEquationalAtomicFactSearchedProofByDefinition2),
    ByBuiltinStrategy(NonEquationalAtomicFactSearchProofByBuiltinStrategy2),
    ByKnownForallFact(NonEquationalAtomicFactSearchedProofByKnownForallFact2),
    ByBuiltinAlgebraicRewrite(NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite2),
    ByKnownAlgebraicRewrite(NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite2),
}

pub struct NonEquationalAtomicFactSearchedProofByKnownAtomicFact2 {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult2>,
}

pub struct NonEquationalAtomicFactSearchedProofByDefinition2 {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

pub struct NonEquationalAtomicFactSearchedProofByKnownForallFact2 {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult2>,
}

impl Runtime {
    pub fn verify_non_equational_atomic_fact2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<VerifyNonEquationalAtomicFactResult2> {
        let well_defined_proof =
            self.verify_atomic_fact_well_definedness2(fact, verify_state.clone())?;
        let searched_proof = match self.verify_atomic_fact_search_proof(fact, verify_state)? {
            VerifyAtomicFactSearchProof2::NonEquationalAtomicFact(proof) => proof,
            VerifyAtomicFactSearchProof2::Equality(_) => {
                unreachable!("a non-equational fact must use the non-equational search pipeline")
            }
        };
        Ok(VerifyNonEquationalAtomicFactResult2 {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_non_equational_atomic_fact_proof2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<NonEquationalAtomicFactSearchedProof2> {
        let _visible_environment_count = self.current_atomic_fact_search_environment_count();

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_cache2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByCache(result));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_builtin_rule2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByBuiltinRule(result));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_atomic_fact2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByKnownAtomicFact(
                result,
            ));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_builtin_strategy2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByBuiltinStrategy(
                result,
            ));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_forall_fact2(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof2::ByKnownForallFact(
                result,
            ));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_builtin_algebraic_rewrite2(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(
                NonEquationalAtomicFactSearchedProof2::ByBuiltinAlgebraicRewrite(result),
            );
        }

        if verify_state.can_use_known_algebraic_rewrite {
            if let Some(result) = self
                .search_non_equational_atomic_proof_by_known_algebraic_rewrite2(fact, verify_state)?
            {
                return Ok(
                    NonEquationalAtomicFactSearchedProof2::ByKnownAlgebraicRewrite(result),
                );
            }
        }

        Err(RuntimeError::Unknown(
            "search_proof: no non-equational atomic proof found".to_string(),
        ))
    }

    pub fn search_non_equational_atomic_proof_by_cache2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<CacheSearchProof2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_rule2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinRule2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_atomic_fact2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchedProofByKnownAtomicFact2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_definition2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchedProofByDefinition2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_strategy2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinStrategy2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_forall_fact2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchedProofByKnownForallFact2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_algebraic_rewrite2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite2>> {
        if let Some(result) =
            self.search_non_equational_atomic_proof_by_builtin_order_dual2(fact, verify_state)?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite2::OrderDual(result),
            ));
        }
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_order_dual2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinOrderDual2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_algebraic_rewrite2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite2>> {
        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_reflexivity2(fact, verify_state.clone())?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite2::Reflexivity(result),
            ));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_known_symmetry2(fact, verify_state)?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite2::Symmetry(result),
            ));
        }

        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_reflexivity2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByKnownReflexivity2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_symmetry2(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState2,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByKnownSymmetry2>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
