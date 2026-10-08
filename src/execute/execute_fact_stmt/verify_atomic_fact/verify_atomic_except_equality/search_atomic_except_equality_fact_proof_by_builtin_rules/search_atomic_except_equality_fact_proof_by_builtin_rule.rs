use crate::ast::fact::{
    AtomicFact, BijectiveFact, CoprimeFact, DvdFact, InjectiveFact, IsChoiceFunctionForFact,
    NotBijectiveFact, NotCoprimeFact, NotDvdFact, NotInjectiveFact, NotIsChoiceFunctionForFact,
    NotIsSetFact, NotPrimeFact, NotProperSubsetFact, NotProperSupersetFact, NotSurjectiveFact,
    PrimeFact, ProperSubsetFact, ProperSupersetFact, SurjectiveFact,
};
use crate::execute::execute_fact_stmt::VerifyState;
use crate::runtime::{Runtime, RuntimeResult};

use super::search_atomic_except_equality_fact_proof_by_builtin_rule_result::{
    AtomicExceptEqualityFactSearchProofByBuiltinRule, BijectiveFactSearchProofByBuiltinRule,
    CoprimeFactSearchProofByBuiltinRule, DvdFactSearchProofByBuiltinRule,
    InjectiveFactSearchProofByBuiltinRule, IsChoiceFunctionForFactSearchProofByBuiltinRule,
    NotBijectiveFactSearchProofByBuiltinRule, NotCoprimeFactSearchProofByBuiltinRule,
    NotDvdFactSearchProofByBuiltinRule, NotInjectiveFactSearchProofByBuiltinRule,
    NotIsChoiceFunctionForFactSearchProofByBuiltinRule, NotIsSetFactSearchProofByBuiltinRule,
    NotPrimeFactSearchProofByBuiltinRule, NotProperSubsetFactSearchProofByBuiltinRule,
    NotProperSupersetFactSearchProofByBuiltinRule, NotSurjectiveFactSearchProofByBuiltinRule,
    PrimeFactSearchProofByBuiltinRule, ProperSubsetFactSearchProofByBuiltinRule,
    ProperSupersetFactSearchProofByBuiltinRule, SurjectiveFactSearchProofByBuiltinRule,
};

impl Runtime {
    pub fn search_atomic_except_equality_fact_proof_by_builtin_rule(
        &mut self,
        fact: &AtomicFact,
        verify_state: VerifyState,
    ) -> RuntimeResult<Option<AtomicExceptEqualityFactSearchProofByBuiltinRule>> {
        match fact {
            AtomicFact::EqualFact(_) => unreachable!(
                "equality facts use the equality search pipeline, not atomic-except-equality builtin rules"
            ),
            AtomicFact::NormalAtomicFact(fact) => Ok(self
                .search_normal_atomic_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NormalAtomicFact)),
            AtomicFact::LessFact(fact) => Ok(self
                .search_less_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessFact)),
            AtomicFact::GreaterFact(fact) => Ok(self
                .search_greater_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterFact)),
            AtomicFact::LessEqualFact(fact) => Ok(self
                .search_less_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::LessEqualFact)),
            AtomicFact::GreaterEqualFact(fact) => Ok(self
                .search_greater_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::GreaterEqualFact)),
            AtomicFact::IsSetFact(fact) => Ok(self
                .search_is_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsSetFact)),
            AtomicFact::IsNonemptySetFact(fact) => Ok(self
                .search_is_nonempty_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsNonemptySetFact)),
            AtomicFact::IsFiniteSetFact(fact) => Ok(self
                .search_is_finite_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsFiniteSetFact)),
            AtomicFact::InFact(fact) => Ok(self
                .search_in_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::InFact)),
            AtomicFact::SubsetFact(fact) => Ok(self
                .search_subset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::SubsetFact)),
            AtomicFact::SupersetFact(fact) => Ok(self
                .search_superset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::SupersetFact)),
            AtomicFact::ProperSubsetFact(fact) => Ok(self
                .search_proper_subset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSubsetFact)),
            AtomicFact::ProperSupersetFact(fact) => Ok(self
                .search_proper_superset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::ProperSupersetFact)),
            AtomicFact::PrimeFact(fact) => Ok(self
                .search_prime_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::PrimeFact)),
            AtomicFact::CoprimeFact(fact) => Ok(self
                .search_coprime_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::CoprimeFact)),
            AtomicFact::DvdFact(fact) => Ok(self
                .search_dvd_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::DvdFact)),
            AtomicFact::InjectiveFact(fact) => Ok(self
                .search_injective_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::InjectiveFact)),
            AtomicFact::SurjectiveFact(fact) => Ok(self
                .search_surjective_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::SurjectiveFact)),
            AtomicFact::BijectiveFact(fact) => Ok(self
                .search_bijective_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::BijectiveFact)),
            AtomicFact::IsChoiceFunctionForFact(fact) => Ok(self
                .search_is_choice_function_for_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::IsChoiceFunctionForFact)),
            AtomicFact::NotNormalAtomicFact(fact) => Ok(self
                .search_not_normal_atomic_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotNormalAtomicFact)),
            AtomicFact::NotEqualFact(fact) => Ok(self
                .search_not_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotEqualFact)),
            AtomicFact::NotLessFact(fact) => Ok(self
                .search_not_less_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessFact)),
            AtomicFact::NotGreaterFact(fact) => Ok(self
                .search_not_greater_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterFact)),
            AtomicFact::NotLessEqualFact(fact) => Ok(self
                .search_not_less_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotLessEqualFact)),
            AtomicFact::NotGreaterEqualFact(fact) => Ok(self
                .search_not_greater_equal_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotGreaterEqualFact)),
            AtomicFact::NotIsSetFact(fact) => Ok(self
                .search_not_is_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsSetFact)),
            AtomicFact::NotIsNonemptySetFact(fact) => Ok(self
                .search_not_is_nonempty_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsNonemptySetFact)),
            AtomicFact::NotIsFiniteSetFact(fact) => Ok(self
                .search_not_is_finite_set_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsFiniteSetFact)),
            AtomicFact::NotInFact(fact) => Ok(self
                .search_not_in_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInFact)),
            AtomicFact::NotSubsetFact(fact) => Ok(self
                .search_not_subset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSubsetFact)),
            AtomicFact::NotSupersetFact(fact) => Ok(self
                .search_not_superset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSupersetFact)),
            AtomicFact::NotProperSubsetFact(fact) => Ok(self
                .search_not_proper_subset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSubsetFact)),
            AtomicFact::NotProperSupersetFact(fact) => Ok(self
                .search_not_proper_superset_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotProperSupersetFact)),
            AtomicFact::NotPrimeFact(fact) => Ok(self
                .search_not_prime_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotPrimeFact)),
            AtomicFact::NotCoprimeFact(fact) => Ok(self
                .search_not_coprime_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotCoprimeFact)),
            AtomicFact::NotDvdFact(fact) => Ok(self
                .search_not_dvd_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotDvdFact)),
            AtomicFact::NotInjectiveFact(fact) => Ok(self
                .search_not_injective_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotInjectiveFact)),
            AtomicFact::NotSurjectiveFact(fact) => Ok(self
                .search_not_surjective_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotSurjectiveFact)),
            AtomicFact::NotBijectiveFact(fact) => Ok(self
                .search_not_bijective_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(AtomicExceptEqualityFactSearchProofByBuiltinRule::NotBijectiveFact)),
            AtomicFact::NotIsChoiceFunctionForFact(fact) => Ok(self
                .search_not_is_choice_function_for_fact_proof_by_builtin_rule(fact, verify_state)?
                .map(
                    AtomicExceptEqualityFactSearchProofByBuiltinRule::NotIsChoiceFunctionForFact,
                )),
        }
    }

    pub fn search_proper_subset_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &ProperSubsetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ProperSubsetFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_proper_superset_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &ProperSupersetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<ProperSupersetFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_dvd_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &DvdFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<DvdFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_injective_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &InjectiveFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<InjectiveFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_surjective_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &SurjectiveFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<SurjectiveFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_bijective_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &BijectiveFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<BijectiveFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_is_choice_function_for_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &IsChoiceFunctionForFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<IsChoiceFunctionForFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_proper_subset_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotProperSubsetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotProperSubsetFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_proper_superset_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotProperSupersetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotProperSupersetFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_dvd_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotDvdFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotDvdFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_injective_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotInjectiveFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotInjectiveFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_surjective_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotSurjectiveFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotSurjectiveFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_bijective_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotBijectiveFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotBijectiveFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_is_choice_function_for_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotIsChoiceFunctionForFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsChoiceFunctionForFactSearchProofByBuiltinRule>> {
        Ok(None)
    }

    pub fn search_not_is_set_fact_proof_by_builtin_rule(
        &mut self,
        _fact: &NotIsSetFact,
        _verify_state: VerifyState,
    ) -> RuntimeResult<Option<NotIsSetFactSearchProofByBuiltinRule>> {
        Ok(None)
    }
}
