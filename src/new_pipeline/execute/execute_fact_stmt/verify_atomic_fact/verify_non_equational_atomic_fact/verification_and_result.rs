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

pub struct VerifyNonEquationalAtomicFactResult {
    pub fact: AtomicFact,
    pub well_defined_proof: DraftAtomicFactWellDefinedProof,
    pub searched_proof: NonEquationalAtomicFactSearchedProof,
}

pub enum NonEquationalAtomicFactSearchedProof {
    ByCache(CacheSearchProof),
    ByBuiltinRule(NonEquationalAtomicFactSearchProofByBuiltinRule),
    ByKnownAtomicFact(NonEquationalAtomicFactSearchedProofByKnownAtomicFact),
    ByDefinition(NonEquationalAtomicFactSearchedProofByDefinition),
    ByBuiltinStrategy(NonEquationalAtomicFactSearchProofByBuiltinStrategy),
    ByKnownForallFact(NonEquationalAtomicFactSearchedProofByKnownForallFact),
    ByBuiltinAlgebraicRewrite(NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite),
    ByKnownAlgebraicRewrite(NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite),
}

pub struct NonEquationalAtomicFactSearchedProofByKnownAtomicFact {
    pub cite_fact_id: FactId,
    pub why_parameters_of_known_fact_are_equal_to_givens: Vec<VerifyFactResult>,
}

pub struct NonEquationalAtomicFactSearchedProofByDefinition {
    pub requirement_facts: Vec<Fact>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

pub struct NonEquationalAtomicFactSearchedProofByKnownForallFact {
    pub cite_fact_id: FactId,
    pub forall_parameters_match_what_args: Vec<Obj>,
    pub proof_of_requirement_facts: Vec<VerifyFactResult>,
}

impl Runtime {
    pub fn verify_non_equational_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<VerifyNonEquationalAtomicFactResult> {
        let well_defined_proof =
            self.verify_draft_atomic_fact_well_definedness(fact, verify_state.clone())?;
        let searched_proof = match self.verify_atomic_fact_search_proof(fact, verify_state)? {
            VerifyAtomicFactSearchProof::NonEquationalAtomicFact(proof) => proof,
            VerifyAtomicFactSearchProof::Equality(_) => {
                unreachable!("a non-equational fact must use the non-equational search pipeline")
            }
        };
        Ok(VerifyNonEquationalAtomicFactResult {
            fact: fact.clone(),
            well_defined_proof,
            searched_proof,
        })
    }

    pub fn search_non_equational_atomic_fact_proof(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<NonEquationalAtomicFactSearchedProof> {
        let _visible_environment_count = self.current_atomic_fact_search_environment_count();

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_cache(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByCache(result));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_builtin_rule(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByBuiltinRule(result));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_atomic_fact(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByKnownAtomicFact(
                result,
            ));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_builtin_strategy(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByBuiltinStrategy(
                result,
            ));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_forall_fact(fact, verify_state.clone())?
        {
            return Ok(NonEquationalAtomicFactSearchedProof::ByKnownForallFact(
                result,
            ));
        }

        if let Some(result) = self
            .search_non_equational_atomic_proof_by_builtin_algebraic_rewrite(
                fact,
                verify_state.clone(),
            )?
        {
            return Ok(
                NonEquationalAtomicFactSearchedProof::ByBuiltinAlgebraicRewrite(result),
            );
        }

        if verify_state.can_use_known_algebraic_rewrite {
            if let Some(result) = self
                .search_non_equational_atomic_proof_by_known_algebraic_rewrite(fact, verify_state)?
            {
                return Ok(
                    NonEquationalAtomicFactSearchedProof::ByKnownAlgebraicRewrite(result),
                );
            }
        }

        Err(RuntimeError::Unknown(
            "search_proof: no non-equational atomic proof found".to_string(),
        ))
    }

    pub fn search_non_equational_atomic_proof_by_cache(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<CacheSearchProof>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_rule(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinRule>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_atomic_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchedProofByKnownAtomicFact>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_definition(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchedProofByDefinition>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_strategy(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinStrategy>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_forall_fact(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchedProofByKnownForallFact>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_algebraic_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite>> {
        if let Some(result) =
            self.search_non_equational_atomic_proof_by_builtin_order_dual(fact, verify_state)?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByBuiltinAlgebraicRewrite::OrderDual(result),
            ));
        }
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_builtin_order_dual(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByBuiltinOrderDual>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_algebraic_rewrite(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite>> {
        if let Some(result) = self
            .search_non_equational_atomic_proof_by_known_reflexivity(fact, verify_state.clone())?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite::Reflexivity(result),
            ));
        }

        if let Some(result) =
            self.search_non_equational_atomic_proof_by_known_symmetry(fact, verify_state)?
        {
            return Ok(Some(
                NonEquationalAtomicFactSearchProofByKnownAlgebraicRewrite::Symmetry(result),
            ));
        }

        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_reflexivity(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByKnownReflexivity>> {
        let _ = (fact, verify_state);
        Ok(None)
    }

    pub fn search_non_equational_atomic_proof_by_known_symmetry(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<NonEquationalAtomicFactSearchProofByKnownSymmetry>> {
        let _ = (fact, verify_state);
        Ok(None)
    }
}
